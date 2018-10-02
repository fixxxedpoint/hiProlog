{-|
Module      : HiProlog.Interpreter
Description : A toy implementation of a Prolog's interpreter.
Copyright   : (c) 2018 Łukasz Lachowski <l.lachowski@gmail.com>
License     : MIT, see the file LICENSE
-}
module HiProlog.Interpreter where


import           Control.Applicative          as A
import           Control.Monad
import           Control.Monad.State          as S
import           Data.Char
import qualified Data.Foldable                as Fold
import           Data.List
import           Data.Maybe
import           Text.ParserCombinators.ReadP as R


type Var = Integer

type AtomName = String
type VarT = AtomName
data Term = App AtomName [Term] | Var VarT deriving (Eq, Read)


instance Show Term where
    showsPrec _ (Var name) = showString name
    showsPrec _ (App name []) = showString name
    showsPrec _ (App name lst) = showString name . showChar '(' . showArgs lst . showChar ')'
      where showArgs = foldr1 (\ a b -> a . showChar ',' . b) . map shows


newtype Subs = Subs [(AtomName, Term)] deriving (Eq, Show)


identitySubs :: Subs
identitySubs = Subs []


data AtomicF = Pred String [Term] deriving (Eq, Read, Show)
data Clause = Clause (Maybe AtomicF) [AtomicF] deriving (Show, Read)
type Program = [Clause]
type Goals = [AtomicF]


data SLDTree = SLDTree { subs :: Subs, goals :: Goals, children :: [SLDTree] } deriving (Eq)


isSuccess :: SLDTree -> Bool
isSuccess (SLDTree subs [] _) = True
isSuccess _                   = False


isFailure :: SLDTree -> Bool
isFailure tree | (not . isSuccess $ tree) && (null . children $ tree) = True
               | otherwise = False


instance Show SLDTree where
    showsPrec ident (SLDTree subs goals subTrees) = foldr (.) id (replicate ident (showString "  ")) .
      shows subs . showChar ' ' .  shows goals . showString "\n" . showSubtrees subTrees
      where showSubtrees = foldr (\ a b -> showsPrec (ident + 1) a . showString "\n" . b) id


solution :: IO ()
solution = do
    programData <- getContents
    let parsedProgram = parseProgram programData
    let (goals, _program) = splitGoalsAndProgram parsedProgram
    let _sldTree = computeSLDTree _program goals
    result <- if null goals && null _program then return empty
              else return $ computeSolution findSolution _sldTree
    print result


splitGoalsAndProgram :: Program -> (Goals, Program)
splitGoalsAndProgram _program = do
  let (goals, program) = partition isGoal _program
  (concatMap toGoal goals, program)
  where isGoal (Clause Nothing (_:_)) = True
        isGoal _                      = False
        toGoal (Clause Nothing _goal)  = _goal


findSolution :: SLDTree -> Maybe [Subs]
findSolution tree | isSuccess tree = Just [subs tree]
                  | isFailure tree = Nothing
findSolution (SLDTree subs _ subTrees) = do
  result <- listToMaybe $ fromJust <$> filter isJust (findSolution <$> subTrees)
  return $ subs : result


findSolutionBfs :: SLDTree -> Maybe [Subs]
findSolutionBfs tree | isSuccess tree = Just [subs tree]
                     | isFailure tree = Nothing
findSolutionBfs tree@(SLDTree subs _ subTrees) = do
    let newTree = sldTreeToPaths (Subs []) tree
        bfsTravers = bfs [newTree]
    (SLDTree subs _ _) <- listToMaybe $ filter isSuccess bfsTravers
    return [subs]


bfs :: [SLDTree] -> [SLDTree]
bfs [] = []
bfs list = list ++ (bfs . concatMap children $ list)


sldTreeToPaths :: Subs -> SLDTree -> SLDTree
sldTreeToPaths solution (SLDTree subs goals subTrees) =
    let newSolution = subs `compose` solution
        newSubTrees = sldTreeToPaths newSolution <$> subTrees
    in SLDTree newSolution goals newSubTrees


composeSolution :: [Subs] -> Subs
composeSolution = foldl (flip compose) identitySubs


narrowSolution :: [VarT] -> Subs -> Subs
narrowSolution vars (Subs subs) = Subs . filter ((`elem` vars) . fst) $ subs


computeSolution :: (SLDTree -> Maybe [Subs]) -> SLDTree -> Maybe Subs
computeSolution finder _sldTree@(SLDTree _ goals _) = do
  _solution <- finder _sldTree
  return $ narrowSolution (freeVariables goals) . composeSolution $ _solution


computeSLDTree :: Program -> Goals -> SLDTree
computeSLDTree _program _goals = evalState (sldTree identitySubs _goals _program) 1


class Terms t where
    freeVariables :: t -> [VarT]
    apply :: Subs -> t -> t


instance (Terms t) => Terms [t] where
    freeVariables = concatMap freeVariables
    apply subs t = apply subs <$> t


instance Terms Clause where
    freeVariables (Clause _head _body) = freeVariables (maybeToList _head) ++ freeVariables _body
    apply subs (Clause _head _body) = Clause (apply subs <$> _head) (apply subs _body)


instance Terms AtomicF where
    freeVariables (Pred _ terms) = freeVariables terms
    apply subs (Pred name terms) = Pred name (apply subs terms)


instance Terms Term where
    freeVariables (App _ terms) = freeVariables terms
    freeVariables (Var var)     = [var]
    apply subs (App name terms)         = App name $ apply subs terms
    apply (Subs subs) var@(Var varName) = fromMaybe var $ lookup varName subs


instance Terms Subs where
    freeVariables (Subs subs) = freeVariables $ map snd subs
    apply subs (Subs val) = Subs $ map ( \ (var, _term) -> (var, apply subs _term) ) val


instantinate :: Clause -> State Var Clause
instantinate _clause = do
    renamed <- rename . freeVariables $ _clause
    return $ apply renamed _clause


rename :: [VarT] -> State Var Subs
rename vars = Subs <$> foldM rename [] vars
  where
    rename subs var = do
      index <- S.get
      put $ index + 1
      let sub = (var, Var ("gnn" ++ show index))
      return $ sub : subs


sldTree :: Subs -> Goals -> Program -> State Var SLDTree
sldTree subs []    _       = return $ SLDTree subs [] []
sldTree subs goals []      = return $ SLDTree subs goals []
sldTree subs goals _program = do
    branches <- Fold.foldrM (generateBranches (goals, _program)) [] _program
    return $ SLDTree subs goals branches


generateBranches :: (Goals, Program) -> Clause -> [SLDTree] -> State Var [SLDTree]
generateBranches (_goal : rest, _program) _clause result = do
    _state <- S.get

    (Clause (Just _head) _body) <- instantinate _clause
    let unification = unifyPredicates _head _goal
    newResult <- if isNothing unification then return result
      else do
        let uResult = fromJust unification
            newGoals = apply uResult (_body ++ rest)
        subTree <- sldTree uResult newGoals _program
        return $ subTree : result

    put _state
    return newResult


unifyPredicates :: AtomicF -> AtomicF -> Maybe Subs
unifyPredicates (Pred name1 terms1) (Pred name2 terms2) | name1 == name2
                                                          && length terms1 == length terms2 =
                                                            unifyTerms $ zip terms1 terms2
                                                        | otherwise      = Nothing


unifyTerms :: [(Term,Term)] -> Maybe Subs
unifyTerms = foldM unify' identitySubs


unify (App s1 arg1) (App s2 arg2) | s1 == s2
                                    && length arg1 == length arg2 =
                                      foldM unify' identitySubs $ zip arg1 arg2
                                  | otherwise = Nothing

unify var@(Var _) t = varBind var t

unify t var@(Var _) = unify var t


unify' subst (v1, v2) = do result <- unify (apply subst v1) (apply subst v2)
                           return $ result `compose` subst


compose subst2@(Subs subst2') subst1 = let (Subs new) = apply subst2 subst1
                                       in Subs $ new ++ subst2'


varBind var@(Var varName) term | var == term              = return identitySubs
                               | var `elem` freeVars term = Nothing
                               | otherwise                = return $ Subs [(varName, term)]


freeVars var@(Var _)  = [var]

freeVars (App _ args) = concatMap freeVars args


followedBy :: ReadP a -> ReadP b -> ReadP a
followedBy p f = p <* f


token :: ReadP a -> ReadP a
token p = skipSpaces *> p <* skipSpaces


symb :: String -> ReadP String
symb = token . string


lower :: ReadP Char
lower = satisfy isLower


upper :: ReadP Char
upper = satisfy isUpper


alphaNum :: ReadP Char
alphaNum = satisfy isAlphaNum


filterStream :: ReadP a -> String -> String
filterStream _ [] = []
filterStream p cs@(s:rest) = remove $ readP_to_S p cs
  where remove []          = s : filterStream p rest
        remove ((_, fs):_) = filterStream p fs


commentBlock :: ReadP String
commentBlock = do
    let startTag = "/*"
        endOfComment = "*/"
    symb startTag
    comment <- A.many $ do
      rest <- look
      let la = take (length endOfComment) rest
      if la == "*/" then empty
                    else R.get
    symb endOfComment <|> eof *> pure ""
    return comment


commentLine :: ReadP String
commentLine =
    symb "%" *> manyTill R.get eof


comments :: ReadP String
comments = commentBlock <|> commentLine


program :: ReadP [Clause]
clause :: ReadP Clause
fact :: ReadP Clause
rule :: ReadP Clause
goal :: ReadP Clause
predicates :: ReadP [AtomicF]
predicate :: ReadP AtomicF
pName :: ReadP String
term :: ReadP Term
fName :: ReadP String
vName :: ReadP String
pfBody :: ReadP [Term]


program = some $ skipSpaces *> clause
clause = fact <|> rule <|> goal
fact = do { _fact <- predicate <* symb "."; return $ Clause (Just _fact) [] }
rule = do { _head <- predicate; symb ":-"; body <- predicates; symb "."; return $ Clause (Just _head) body }
goal = symb ":-" *> predicates <* symb "." <**> pure (Clause Nothing)
predicates = predicate `sepBy1` symb ","
predicate = Pred <$> pName <*> (skipSpaces *> pfBody)
pName = (:) <$> lower <*> A.many alphaNum
term = ( App <$> fName <*> (skipSpaces *> pfBody) )
   <|> ( App <$> fName <*> pure [] )
   <|> ( Var <$> vName )
fName = pName
vName = (:) <$> upper <*> A.many alphaNum
pfBody = symb "(" *> term `sepBy1` (skipSpaces *> symb ",") <* skipSpaces <* symb ")"


parseProgram :: String -> Program
parseProgram programData =
    let withoutBlockComments = filterStream commentBlock programData
        programLines = lines withoutBlockComments
        withoutComments = unlines $ filterStream commentLine <$> programLines
        result = readP_to_S (program <* eof) withoutComments
    in if null result then empty
                      else fst . head $ result
