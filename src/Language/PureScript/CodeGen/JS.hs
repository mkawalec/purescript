-- | This module generates code in the core imperative representation from
-- elaborated PureScript code.
module Language.PureScript.CodeGen.JS
  ( module AST
  , module Common
  , moduleToJs
  ) where

import Prelude.Compat
import Protolude (ordNub)

import Control.Arrow ((&&&))
import Control.Monad (forM, foldM, replicateM, void)
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.Reader (MonadReader, asks)
import Control.Monad.Supply.Class

import Data.List ((\\), delete, intersect)
import qualified Data.Foldable as F
import qualified Data.Map as M
import Data.Maybe (fromMaybe, isNothing)
import Data.Monoid ((<>))
import Data.String (fromString)
import Data.Text (Text)
import qualified Data.Text as T

import Language.PureScript.AST.SourcePos
import Language.PureScript.CodeGen.JS.Common as Common
import Language.PureScript.CoreImp.AST (AST, everywhereTopDownM, withSourceSpan)
import qualified Language.PureScript.CoreImp.AST as AST
import Language.PureScript.CoreImp.Optimizer
import Language.PureScript.CoreFn
import Language.PureScript.Crash
import Language.PureScript.Externs (Acc(..))
import Language.PureScript.Errors (ErrorMessageHint(..), SimpleErrorMessage(..),
                                   MultipleErrors(..), rethrow,
                                   errorMessage, rethrowWithPosition, addHint)
import Language.PureScript.Names
import Language.PureScript.Options
import Language.PureScript.PSString (PSString, mkString)
import Language.PureScript.Traversals (sndM)
import qualified Language.PureScript.Constants as C

import System.FilePath.Posix ((</>))
import qualified Debug.Trace as DT
import qualified Text.Show.Pretty as P

-- | Generate code in the simplified JavaScript intermediate representation for all declarations in a
-- module.
moduleToJs
  :: forall m
   . (Monad m, MonadReader Options m, MonadSupply m, MonadError MultipleErrors m)
  => Module Ann
  -> Maybe AST
  -> m ([AST], M.Map Acc Int)
moduleToJs (Module coms mn _ imps exps foreigns decls) foreign_ =
  rethrow (addHint (ErrorInModule mn)) $ do
    let usedNames = concatMap getNames decls
    let mnLookup = renameImports usedNames imps
    jsImports <- traverse (importToJs mnLookup) . delete (ModuleName [ProperName C.prim]) . (\\ [mn]) $ ordNub $ map snd imps
    let decls' = renameModules mnLookup decls

    let step (m', asts) val = bindToJs m' val >>= return . mapSnd (:asts)
    (bindingMap, jsDecls) <- mapSnd reverse <$> foldM step (M.empty, []) decls'

    optimized <- traverse (traverse optimize) jsDecls
    F.traverse_ (F.traverse_ checkIntegers) optimized
    comments <- not <$> asks optionsNoComments
    let strict = AST.StringLiteral Nothing "use strict"
    let header = if comments && not (null coms) then AST.Comment Nothing coms strict else strict
    let foreign' = [AST.VariableIntroduction Nothing "$foreign" foreign_ | not $ null foreigns || isNothing foreign_]
    let moduleBody = header : foreign' ++ jsImports ++ concat optimized
    let foreignExps = exps `intersect` foreigns
    let standardExps = exps \\ foreignExps
    let exps' = AST.ObjectLiteral Nothing $ map (mkString . runIdent &&& AST.Var Nothing . identToJs) standardExps
                               ++ map (mkString . runIdent &&& foreignIdent) foreignExps
    return $ (moduleBody ++ [AST.Assignment Nothing (accessorString "exports" (AST.Var Nothing "module")) exps'], bindingMap)

  where

  -- | Extracts all declaration names from a binding group.
  getNames :: Bind Ann -> [Ident]
  getNames (NonRec _ ident _) = [ident]
  getNames (Rec vals) = map (snd . fst) vals

  -- | Creates alternative names for each module to ensure they don't collide
  -- with declaration names.
  renameImports :: [Ident] -> [(Ann, ModuleName)] -> M.Map ModuleName (Ann, ModuleName)
  renameImports = go M.empty
    where
    go :: M.Map ModuleName (Ann, ModuleName) -> [Ident] -> [(Ann, ModuleName)] -> M.Map ModuleName (Ann, ModuleName)
    go acc used ((ann, mn') : mns') =
      let mni = Ident $ runModuleName mn'
      in if mn' /= mn && mni `elem` used
         then let newName = freshModuleName 1 mn' used
              in go (M.insert mn' (ann, newName) acc) (Ident (runModuleName newName) : used) mns'
         else go (M.insert mn' (ann, mn') acc) used mns'
    go acc _ [] = acc

    freshModuleName :: Integer -> ModuleName -> [Ident] -> ModuleName
    freshModuleName i mn'@(ModuleName pns) used =
      let newName = ModuleName $ init pns ++ [ProperName $ runProperName (last pns) <> "_" <> T.pack (show i)]
      in if Ident (runModuleName newName) `elem` used
         then freshModuleName (i + 1) mn' used
         else newName

  -- | Generates JavaScript code for a module import, binding the required module
  -- to the alternative
  importToJs :: M.Map ModuleName (Ann, ModuleName) -> ModuleName -> m AST
  importToJs mnLookup mn' = do
    let ((ss, _, _, _), mnSafe) = fromMaybe (internalError "Missing value in mnLookup") $ M.lookup mn' mnLookup
    let moduleBody = AST.App Nothing (AST.Var Nothing "require") [AST.StringLiteral Nothing (fromString (".." </> T.unpack (runModuleName mn')))]
    withPos ss $ AST.VariableIntroduction Nothing (moduleNameToJs mnSafe) (Just moduleBody)

  -- | Replaces the `ModuleName`s in the AST so that the generated code refers to
  -- the collision-avoiding renamed module imports.
  renameModules :: M.Map ModuleName (Ann, ModuleName) -> [Bind Ann] -> [Bind Ann]
  renameModules mnLookup binds =
    let (f, _, _) = everywhereOnValues id goExpr goBinder
    in map f binds
    where
    goExpr :: Expr a -> Expr a
    goExpr (Var ann q) = Var ann (renameQual q)
    goExpr e = e
    goBinder :: Binder a -> Binder a
    goBinder (ConstructorBinder ann q1 q2 bs) = ConstructorBinder ann (renameQual q1) (renameQual q2) bs
    goBinder b = b
    renameQual :: Qualified a -> Qualified a
    renameQual (Qualified (Just mn') a) =
      let (_,mnSafe) = fromMaybe (internalError "Missing value in mnLookup") $ M.lookup mn' mnLookup
      in Qualified (Just mnSafe) a
    renameQual q = q

  mapSnd :: (b -> c) -> (a , b) -> (a, c)
  mapSnd f (a, b) = (a, f b)

  -- |
  -- Generate code in the simplified JavaScript intermediate representation for a declaration
  --
  bindToJs :: M.Map Acc Int -> Bind Ann -> m (M.Map Acc Int, [AST])
  bindToJs m (NonRec ann ident val) = do
    (m', ast) <- nonRecToJS m ann ident val
    return (m', [ast])
  bindToJs m (Rec vals) = (mapSnd reverse) <$> foldM step (m, []) vals
    where step (m', asts) val = do
                (m'', ast) <- (uncurry . uncurry $ nonRecToJS m') val
                return (m'', ast:asts)

  -- | Generate code in the simplified JavaScript intermediate representation for a single non-recursive
  -- declaration.
  --
  -- The main purpose of this function is to handle code generation for comments.
  nonRecToJS :: M.Map Acc Int -> Ann -> Ident -> Expr Ann -> m (M.Map Acc Int, AST)
  nonRecToJS m a i e@(extractAnn -> (_, com, _, _)) | not (null com) = do
    withoutComment <- asks optionsNoComments
    if withoutComment
       then nonRecToJS m a i (modifyAnn removeComments e)
       else do
         (m', ast) <- nonRecToJS m a i (modifyAnn removeComments e)
         return (m', AST.Comment Nothing com ast)
  nonRecToJS m (ss, _, _, _) ident val = do
    (argCount, m') <- countArgs m ident [] val
    let m'' = case argCount of
                Just args -> M.insert (Acc ident []) args m'
                Nothing ->  m'
    js <- valueToJs m'' val
    ast <- withPos ss $ AST.VariableIntroduction Nothing (identToJs ident) (Just js)
    return (m'', ast)

  countArgs :: M.Map Acc Int -> Ident -> [PSString] -> Expr Ann -> m ((Maybe Int), M.Map Acc Int)
  countArgs m _ _ expr@Abs{} =
    let getArgs (Abs _ arg' val') = arg':args'
            where args' = getArgs val'
        getArgs _ = []
        argCount = length $ getArgs expr
    in return $ (Just argCount, m)
  countArgs m _ _ app@App{} = return $ case unApp app [] of
    (Var _ (Qualified _ ident), args) -> case M.lookup (Acc ident []) m of
                                          Just argC -> (Just (argC - length args), m)
                                          Nothing -> (Nothing, m)
    _ -> (Nothing, m)
  countArgs m ident path (Let _ bindings expr) = DT.trace ("let " ++ (P.ppShow expr)) $ do
    m'' <- foldM (\m' binding -> fst <$> bindToJs m' binding) m bindings
    countArgs m'' ident path expr
  countArgs m ident path (Case _ _ ((CaseAlternative {caseAlternativeResult=(Right res)}):_)) = countArgs m ident path res
  countArgs m ident path (Literal _ (ObjectLiteral keys)) = do
    newMap <- foldM (\m' (key, contents) -> do
      (args, m'') <- countArgs m' ident (key:path) contents
      let finalMap = case args of
                      Just argCount -> M.insert (Acc ident (key:path)) argCount m''
                      Nothing -> m''
      return finalMap) m keys
    return $ (Nothing, newMap)
  countArgs m _ _ _ = return $ (Nothing, m)

  withPos :: SourceSpan -> AST -> m AST
  withPos ss js = do
    withSM <- asks optionsSourceMaps
    return $ if withSM
      then withSourceSpan ss js
      else js

  -- | Generate code in the simplified JavaScript intermediate representation for a variable based on a
  -- PureScript identifier.
  var :: Ident -> AST
  var = AST.Var Nothing . identToJs

  -- | Generate code in the simplified JavaScript intermediate representation for an accessor based on
  -- a PureScript identifier. If the name is not valid in JavaScript (symbol based, reserved name) an
  -- indexer is returned.
  accessor :: Ident -> AST -> AST
  accessor (Ident prop) = accessorString $ mkString prop
  accessor (GenIdent _ _) = internalError "GenIdent in accessor"

  accessorString :: PSString -> AST -> AST
  accessorString prop = AST.Indexer Nothing (AST.StringLiteral Nothing prop)

  -- | Generate code in the simplified JavaScript intermediate representation for a value or expression.
  valueToJs :: M.Map Acc Int -> Expr Ann -> m AST
  valueToJs m e =
    let (ss, _, _, _) = extractAnn e in
    withPos ss =<< valueToJs' m e

  valueToJs' :: M.Map Acc Int -> Expr Ann -> m AST
  valueToJs' m (Literal (pos, _, _, _) l) =
    rethrowWithPosition pos $ literalToValueJS m l
  valueToJs' _ (Var (_, _, _, Just (IsConstructor _ [])) name) =
    return $ accessorString "value" $ qualifiedToJS id name
  valueToJs' _ (Var (_, _, _, Just (IsConstructor _ _)) name) =
    return $ accessorString "create" $ qualifiedToJS id name
  valueToJs' m (Accessor _ prop val) =
    accessorString prop <$> valueToJs m val
  valueToJs' m (ObjectUpdate _ o ps) = do
    obj <- valueToJs m o
    sts <- mapM (sndM $ valueToJs m) ps
    extendObj obj sts
  valueToJs' _ e@(Abs (_, _, _, Just IsTypeClassConstructor) _ _) =
    let args = unAbs e
    in return $ AST.Function Nothing Nothing (map identToJs args) (AST.Block Nothing $ map assign args)
    where
    unAbs :: Expr Ann -> [Ident]
    unAbs (Abs _ arg val) = arg : unAbs val
    unAbs _ = []
    assign :: Ident -> AST
    assign name = AST.Assignment Nothing (accessorString (mkString $ runIdent name) (AST.Var Nothing "this"))
                               (var name)
  valueToJs' m (Abs _ arg val) =
    let getArgs (Abs _ arg' val') = (arg':args', res)
            where (args', res) = getArgs val'
        getArgs otherThing = ([], otherThing)
    in do
      let (args, val') = getArgs val
      ret <- valueToJs m val'
      return $ AST.Function Nothing Nothing (map identToJs (arg:args)) (AST.Block Nothing [AST.Return Nothing ret])
  valueToJs' m e@App{} = do
    let (f, args) = unApp e []
    args' <- mapM (valueToJs m) args
    case f of
      Var (_, _, _, Just IsNewtype) _ -> return (head args')
      Var (_, _, _, Just (IsConstructor _ fields)) name | length args == length fields ->
        return $ AST.Unary Nothing AST.New $ AST.App Nothing (qualifiedToJS id name) args'
      Var (_, _, _, Just IsTypeClassConstructor) name ->
        return $ AST.Unary Nothing AST.New $ AST.App Nothing (qualifiedToJS id name) args'
      Var _ (Qualified _ ident) -> do
        ret <- valueToJs m f
        return $ case M.lookup (Acc ident []) m of
          Just argCount -> if argCount > length args'
                            then AST.App Nothing (AST.Indexer Nothing (AST.StringLiteral Nothing $ mkString "bind") ret) ((AST.Var Nothing "null"):args')
                            else AST.App Nothing ret args'
          Nothing -> AST.App Nothing ret args'
      acc@Accessor{} -> do
        let unAcc path (Accessor _ key rest) = unAcc (key:path) rest
            unAcc path (Var _ (Qualified _ ident)) = Just (ident, path)
            unAcc _ _ = Nothing
        ret <- DT.trace ("accessor " ++ (show $ unAcc [] acc) ++ " " ++ (show m)) valueToJs m f
        return $ case unAcc [] acc of
          Just (ident, path) -> do
            case M.lookup (Acc ident (reverse path)) m of
              Just argCount -> if argCount > length args'
                                then AST.App Nothing (AST.Indexer Nothing (AST.StringLiteral Nothing $ mkString "bind") ret) ((AST.Var Nothing "null"):args')
                                else AST.App Nothing ret args'
              Nothing -> AST.App Nothing ret args'
          Nothing -> AST.App Nothing ret args'
      _ -> do
        ret <- valueToJs m f
        return $ AST.App Nothing ret args'
  valueToJs' _ (Var (_, _, _, Just IsForeign) qi@(Qualified (Just mn') ident)) =
    return $ if mn' == mn
             then foreignIdent ident
             else varToJs qi
  valueToJs' _ (Var (_, _, _, Just IsForeign) ident) =
    internalError $ "Encountered an unqualified reference to a foreign ident " ++ T.unpack (showQualified showIdent ident)
  valueToJs' _ (Var _ ident) = return $ varToJs ident
  valueToJs' m (Case (ss, _, _, _) values binders) = do
    vals <- mapM (valueToJs m) values
    bindersToJs m ss binders vals
  valueToJs' m (Let _ ds val) = do
    let step (m', asts) d = bindToJs m' d >>= return . mapSnd (:asts)
    (m', ds') <- (mapSnd (concat . reverse)) <$> foldM step (m, []) ds
    ret <- valueToJs m' val
    return $ AST.App Nothing (AST.Function Nothing Nothing [] (AST.Block Nothing (ds' ++ [AST.Return Nothing ret]))) []
  valueToJs' _ (Constructor (_, _, _, Just IsNewtype) _ (ProperName ctor) _) =
    return $ AST.VariableIntroduction Nothing (properToJs ctor) (Just $
                AST.ObjectLiteral Nothing [("create",
                  AST.Function Nothing Nothing ["value"]
                    (AST.Block Nothing [AST.Return Nothing $ AST.Var Nothing "value"]))])
  valueToJs' _ (Constructor _ _ (ProperName ctor) []) =
    return $ iife (properToJs ctor) [ AST.Function Nothing (Just (properToJs ctor)) [] (AST.Block Nothing [])
           , AST.Assignment Nothing (accessorString "value" (AST.Var Nothing (properToJs ctor)))
                (AST.Unary Nothing AST.New $ AST.App Nothing (AST.Var Nothing (properToJs ctor)) []) ]
  valueToJs' _ (Constructor _ _ (ProperName ctor) fields) =
    let constructor =
          let body = [ AST.Assignment Nothing ((accessorString $ mkString $ identToJs f) (AST.Var Nothing "this")) (var f) | f <- fields ]
          in AST.Function Nothing (Just (properToJs ctor)) (identToJs `map` fields) (AST.Block Nothing body)
        createFn =
          let body = AST.Unary Nothing AST.New $ AST.App Nothing (AST.Var Nothing (properToJs ctor)) (var `map` fields)
          in foldr (\f inner -> AST.Function Nothing Nothing [identToJs f] (AST.Block Nothing [AST.Return Nothing inner])) body fields
    in return $ iife (properToJs ctor) [ constructor
                          , AST.Assignment Nothing (accessorString "create" (AST.Var Nothing (properToJs ctor))) createFn
                          ]

  unApp :: Expr Ann -> [Expr Ann] -> (Expr Ann, [Expr Ann])
  unApp (App _ val arg) args = unApp val (arg : args)
  unApp other args = (other, args)

  iife :: Text -> [AST] -> AST
  iife v exprs = AST.App Nothing (AST.Function Nothing Nothing [] (AST.Block Nothing $ exprs ++ [AST.Return Nothing $ AST.Var Nothing v])) []

  literalToValueJS :: M.Map Acc Int -> Literal (Expr Ann) -> m AST
  literalToValueJS _ (NumericLiteral (Left i)) = return $ AST.NumericLiteral Nothing (Left i)
  literalToValueJS _ (NumericLiteral (Right n)) = return $ AST.NumericLiteral Nothing (Right n)
  literalToValueJS _ (StringLiteral s) = return $ AST.StringLiteral Nothing s
  literalToValueJS _ (CharLiteral c) = return $ AST.StringLiteral Nothing (fromString [c])
  literalToValueJS _ (BooleanLiteral b) = return $ AST.BooleanLiteral Nothing b
  literalToValueJS m (ArrayLiteral xs) = AST.ArrayLiteral Nothing <$> mapM (valueToJs m) xs
  literalToValueJS m (ObjectLiteral ps) = AST.ObjectLiteral Nothing <$> mapM (sndM $ valueToJs m) ps

  -- | Shallow copy an object.
  extendObj :: AST -> [(PSString, AST)] -> m AST
  extendObj obj sts = do
    newObj <- freshName
    key <- freshName
    evaluatedObj <- freshName
    let
      jsKey = AST.Var Nothing key
      jsNewObj = AST.Var Nothing newObj
      jsEvaluatedObj = AST.Var Nothing evaluatedObj
      block = AST.Block Nothing (evaluate:objAssign:copy:extend ++ [AST.Return Nothing jsNewObj])
      evaluate = AST.VariableIntroduction Nothing evaluatedObj (Just obj)
      objAssign = AST.VariableIntroduction Nothing newObj (Just $ AST.ObjectLiteral Nothing [])
      copy = AST.ForIn Nothing key jsEvaluatedObj $ AST.Block Nothing [AST.IfElse Nothing cond assign Nothing]
      cond = AST.App Nothing (accessorString "call" (accessorString "hasOwnProperty" (AST.ObjectLiteral Nothing []))) [jsEvaluatedObj, jsKey]
      assign = AST.Block Nothing [AST.Assignment Nothing (AST.Indexer Nothing jsKey jsNewObj) (AST.Indexer Nothing jsKey jsEvaluatedObj)]
      stToAssign (s, js) = AST.Assignment Nothing (accessorString s jsNewObj) js
      extend = map stToAssign sts
    return $ AST.App Nothing (AST.Function Nothing Nothing [] block) []

  -- | Generate code in the simplified JavaScript intermediate representation for a reference to a
  -- variable.
  varToJs :: Qualified Ident -> AST
  varToJs (Qualified Nothing ident) = var ident
  varToJs qual = qualifiedToJS id qual

  -- | Generate code in the simplified JavaScript intermediate representation for a reference to a
  -- variable that may have a qualified name.
  qualifiedToJS :: (a -> Ident) -> Qualified a -> AST
  qualifiedToJS f (Qualified (Just (ModuleName [ProperName mn'])) a) | mn' == C.prim = AST.Var Nothing . runIdent $ f a
  qualifiedToJS f (Qualified (Just mn') a) | mn /= mn' = accessor (f a) (AST.Var Nothing (moduleNameToJs mn'))
  qualifiedToJS f (Qualified _ a) = AST.Var Nothing $ identToJs (f a)

  foreignIdent :: Ident -> AST
  foreignIdent ident = accessorString (mkString $ runIdent ident) (AST.Var Nothing "$foreign")

  -- | Generate code in the simplified JavaScript intermediate representation for pattern match binders
  -- and guards.
  bindersToJs :: M.Map Acc Int -> SourceSpan -> [CaseAlternative Ann] -> [AST] -> m AST
  bindersToJs m ss binders vals = do
    valNames <- replicateM (length vals) freshName
    let assignments = zipWith (AST.VariableIntroduction Nothing) valNames (map Just vals)
    jss <- forM binders $ \(CaseAlternative bs result) -> do
      ret <- guardsToJs m result
      go valNames ret bs
    return $ AST.App Nothing (AST.Function Nothing Nothing [] (AST.Block Nothing (assignments ++ concat jss ++ [AST.Throw Nothing $ failedPatternError valNames])))
                   []
    where
      go :: [Text] -> [AST] -> [Binder Ann] -> m [AST]
      go _ done [] = return done
      go (v:vs) done' (b:bs) = do
        done'' <- go vs done' bs
        binderToJs v done'' b
      go _ _ _ = internalError "Invalid arguments to bindersToJs"

      failedPatternError :: [Text] -> AST
      failedPatternError names = AST.Unary Nothing AST.New $ AST.App Nothing (AST.Var Nothing "Error") [AST.Binary Nothing AST.Add (AST.StringLiteral Nothing $ mkString failedPatternMessage) (AST.ArrayLiteral Nothing $ zipWith valueError names vals)]

      failedPatternMessage :: Text
      failedPatternMessage = "Failed pattern match at " <> runModuleName mn <> " " <> displayStartEndPos ss <> ": "

      valueError :: Text -> AST -> AST
      valueError _ l@(AST.NumericLiteral _ _) = l
      valueError _ l@(AST.StringLiteral _ _)  = l
      valueError _ l@(AST.BooleanLiteral _ _) = l
      valueError s _                        = accessorString "name" . accessorString "constructor" $ AST.Var Nothing s

      guardsToJs :: M.Map Acc Int -> Either [(Guard Ann, Expr Ann)] (Expr Ann) -> m [AST]
      guardsToJs m' (Left gs) = traverse genGuard gs where
        genGuard (cond, val) = do
          cond' <- valueToJs m' cond
          val'   <- valueToJs m' val
          return
            (AST.IfElse Nothing cond'
              (AST.Block Nothing [AST.Return Nothing val']) Nothing)

      guardsToJs m' (Right v) = return . AST.Return Nothing <$> valueToJs m' v

  binderToJs :: Text -> [AST] -> Binder Ann -> m [AST]
  binderToJs s done binder =
    let (ss, _, _, _) = extractBinderAnn binder in
    traverse (withPos ss) =<< binderToJs' s done binder

  -- | Generate code in the simplified JavaScript intermediate representation for a pattern match
  -- binder.
  binderToJs' :: Text -> [AST] -> Binder Ann -> m [AST]
  binderToJs' _ done NullBinder{} = return done
  binderToJs' varName done (LiteralBinder _ l) =
    literalToBinderJS varName done l
  binderToJs' varName done (VarBinder _ ident) =
    return (AST.VariableIntroduction Nothing (identToJs ident) (Just (AST.Var Nothing varName)) : done)
  binderToJs' varName done (ConstructorBinder (_, _, _, Just IsNewtype) _ _ [b]) =
    binderToJs varName done b
  binderToJs' varName done (ConstructorBinder (_, _, _, Just (IsConstructor ctorType fields)) _ ctor bs) = do
    js <- go (zip fields bs) done
    return $ case ctorType of
      ProductType -> js
      SumType ->
        [AST.IfElse Nothing (AST.InstanceOf Nothing (AST.Var Nothing varName) (qualifiedToJS (Ident . runProperName) ctor))
                  (AST.Block Nothing js)
                  Nothing]
    where
    go :: [(Ident, Binder Ann)] -> [AST] -> m [AST]
    go [] done' = return done'
    go ((field, binder) : remain) done' = do
      argVar <- freshName
      done'' <- go remain done'
      js <- binderToJs argVar done'' binder
      return (AST.VariableIntroduction Nothing argVar (Just $ accessorString (mkString $ identToJs field) $ AST.Var Nothing varName) : js)
  binderToJs' _ _ ConstructorBinder{} =
    internalError "binderToJs: Invalid ConstructorBinder in binderToJs"
  binderToJs' varName done (NamedBinder _ ident binder) = do
    js <- binderToJs varName done binder
    return (AST.VariableIntroduction Nothing (identToJs ident) (Just (AST.Var Nothing varName)) : js)

  literalToBinderJS :: Text -> [AST] -> Literal (Binder Ann) -> m [AST]
  literalToBinderJS varName done (NumericLiteral num) =
    return [AST.IfElse Nothing (AST.Binary Nothing AST.EqualTo (AST.Var Nothing varName) (AST.NumericLiteral Nothing num)) (AST.Block Nothing done) Nothing]
  literalToBinderJS varName done (CharLiteral c) =
    return [AST.IfElse Nothing (AST.Binary Nothing AST.EqualTo (AST.Var Nothing varName) (AST.StringLiteral Nothing (fromString [c]))) (AST.Block Nothing done) Nothing]
  literalToBinderJS varName done (StringLiteral str) =
    return [AST.IfElse Nothing (AST.Binary Nothing AST.EqualTo (AST.Var Nothing varName) (AST.StringLiteral Nothing str)) (AST.Block Nothing done) Nothing]
  literalToBinderJS varName done (BooleanLiteral True) =
    return [AST.IfElse Nothing (AST.Var Nothing varName) (AST.Block Nothing done) Nothing]
  literalToBinderJS varName done (BooleanLiteral False) =
    return [AST.IfElse Nothing (AST.Unary Nothing AST.Not (AST.Var Nothing varName)) (AST.Block Nothing done) Nothing]
  literalToBinderJS varName done (ObjectLiteral bs) = go done bs
    where
    go :: [AST] -> [(PSString, Binder Ann)] -> m [AST]
    go done' [] = return done'
    go done' ((prop, binder):bs') = do
      propVar <- freshName
      done'' <- go done' bs'
      js <- binderToJs propVar done'' binder
      return (AST.VariableIntroduction Nothing propVar (Just (accessorString prop (AST.Var Nothing varName))) : js)
  literalToBinderJS varName done (ArrayLiteral bs) = do
    js <- go done 0 bs
    return [AST.IfElse Nothing (AST.Binary Nothing AST.EqualTo (accessorString "length" (AST.Var Nothing varName)) (AST.NumericLiteral Nothing (Left (fromIntegral $ length bs)))) (AST.Block Nothing js) Nothing]
    where
    go :: [AST] -> Integer -> [Binder Ann] -> m [AST]
    go done' _ [] = return done'
    go done' index (binder:bs') = do
      elVar <- freshName
      done'' <- go done' (index + 1) bs'
      js <- binderToJs elVar done'' binder
      return (AST.VariableIntroduction Nothing elVar (Just (AST.Indexer Nothing (AST.NumericLiteral Nothing (Left index)) (AST.Var Nothing varName))) : js)

  -- Check that all integers fall within the valid int range for JavaScript.
  checkIntegers :: AST -> m ()
  checkIntegers = void . everywhereTopDownM go
    where
    go :: AST -> m AST
    go (AST.Unary _ AST.Negate (AST.NumericLiteral ss (Left i))) =
      -- Move the negation inside the literal; since this is a top-down
      -- traversal doing this replacement will stop the next case from raising
      -- the error when attempting to use -2147483648, as if left unrewritten
      -- the value is `Unary Negate (NumericLiteral (Left 2147483648))`, and
      -- 2147483648 is larger than the maximum allowed int.
      return $ AST.NumericLiteral ss (Left (-i))
    go js@(AST.NumericLiteral _ (Left i)) =
      let minInt = -2147483648
          maxInt = 2147483647
      in if i < minInt || i > maxInt
         then throwError . errorMessage $ IntOutOfRange i "JavaScript" minInt maxInt
         else return js
    go other = return other
