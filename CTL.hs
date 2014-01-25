{-# LANGUAGE TemplateHaskell #-}
module CTL where

import Test.QuickCheck
import Test.QuickCheck.All
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Map (Map)
import Data.Set (Set)

type State = Int

type States = Set State
type Transitions = Map State (Set State)
type Label = String
type Labels = Map State (Set Label)
type M = (States, Transitions, Labels)

infixr 8 <>

(<>) :: (M,State) -> State -> Bool
(<>) ((_,mt,_),s) s' = case M.lookup s mt of 
                         Nothing -> False
                         Just v -> s' `S.member` v

states :: M -> [State]
states (s,_,_) = S.toList s

successors :: M -> State -> [State]
successors (_,mt,_) s = case M.lookup s mt of
                          Nothing -> []
                          Just v -> S.toList v

preE :: M -> Set State -> Set State
preE m y = S.fromList [ s | s <- states m, anyInY (successors m s) y ]

anyInY s y = foldr (\succ acc -> (succ `S.member` y || acc)) False s

preA :: M -> Set State -> Set State
preA m@(states,_,_) y = S.fromList [ s | s <- S.toList states, all (check s) (successors m s)]
    where check s s' = (m,s) <> s' && s' `S.member` y

type Var = String

data CTL = CTrue
         | CFalse
         | Atom Var
         | CNot CTL
         | And CTL CTL
         | Or  CTL CTL
         | Impl CTL CTL
         | AX CTL
         | EX CTL
         | AU CTL CTL
         | EU CTL CTL
         | EF CTL
         | EG CTL
         | AF CTL
         | AG CTL

(<+>) :: CTL -> CTL -> CTL
(<+>) = Or
(<*>) :: CTL -> CTL -> CTL
(<*>) = And

sat :: M -> CTL -> Set State
sat (s,_,_) CTrue  = s
sat _       CFalse = S.empty
sat m@(s,_,_) (CNot phi) = s `S.difference` sat m phi
sat (s,_,l) (Atom v) = S.fromList [s' | s' <- S.toList s, check s' v]
    where check s v = case M.lookup s l of
                       Nothing -> False
                       Just ls -> v `S.member` ls 
sat m (And x y) = sat m x `S.intersection` sat m y
sat m (Or x y)  = sat m x `S.union` sat m y
sat m (Impl x y) = sat m (CNot x `Or` y)
-- duality AX x == -EX -x
sat m (AX x) = sat m (CNot $ EX $ CNot x)
sat m (EX x) = satEX m x
sat m (AU x y) = sat m $ CNot $ EU (CNot y) (CNot x `And` CNot y) `Or` (EG $ CNot y)
sat m (EU x y) = satEU m x y
sat m (EF x) = sat m (EU CTrue x)
sat m (EG x) = sat m (CNot $ AG $ CNot x)
sat m (AF x) = satAF m x
sat m (AG x) = sat m (CNot $ EF $ CNot x)

satEX :: M -> CTL -> Set State
satEX m phi = preE m s'
    where s' = sat m phi 

satEU :: M -> CTL -> CTL -> Set State
satEU m x y = satEU' ends m possiblePrefixes
    where ends = sat m y
          possiblePrefixes = sat m x

satEU' :: Set State -> M -> Set State -> Set State
satEU' accum m prefixes = if accum == all then all else satEU' all m prefixes
    where precs = preE m accum
          all = accum `S.union` (precs `S.intersection` prefixes)

satAF :: M -> CTL -> Set State
satAF m phi = satAF' m phi S.empty

satAF' :: M -> CTL -> Set State -> Set State
satAF' m phi acc = if acc == f 
                    then acc
                    else satAF' m phi f
    where direct = sat m phi
          prec = preA m direct
          f = direct `S.union` prec

(--->) :: State -> State -> (State, Set State)
(--->) s s' = (s, S.singleton s')

trans :: [(State,Set State)] -> Map State (Set State)
trans  = foldr (\(s,sx') acc -> case M.lookup s acc of
                                   Nothing -> M.insert s sx' acc
                                   Just v -> M.update (\targets -> Just $ v `S.union` sx') s acc) M.empty 

(<--) :: State -> Label -> (State,Set Label)
(<--) s l = (s, S.singleton l)

lbls :: [(State,Set Label)] -> Map State (Set Label)
lbls = M.fromList

m1 = (S.fromList [1,2,3], 
      trans [1 ---> 2, 2 ---> 3, 3 ---> 3], 
      lbls [ 1 <-- "a" ] )

m2 = (S.fromList [1,2,3,4,5], 
      trans [1 ---> 2, 2 ---> 3, 2 ---> 4, 3 ---> 3, 4 ---> 4, 1 ---> 5, 5 ---> 5], 
      lbls [ 3 <-- "a", 4 <-- "a" ] )

m3 :: M
m3 = (S.fromList [1,2,3,4,5], 
      trans [1 ---> 2, 2 ---> 3, 2 ---> 4, 3 ---> 3, 4 ---> 4, 1 ---> 5, 5 ---> 5], 
      lbls [ 3 <-- "a" ] )

m4 :: M
m4 = (S.fromList [1,2,3,4,5], 
      trans [1 ---> 2, 2 ---> 3, 2 ---> 4, 3 ---> 3, 4 ---> 4, 1 ---> 5, 5 ---> 5], 
      lbls [ 1 <-- "a", 2 <-- "a", 3 <-- "b" ] )

m5 :: M
m5 = (S.fromList [1,2,3,4,5], 
      trans [1 ---> 2, 2 ---> 3, 2 ---> 4, 3 ---> 3, 4 ---> 4, 1 ---> 5, 5 ---> 5], 
      lbls [ 1 <-- "a", 2 <-- "a", 3 <-- "b", 4 <-- "b" ] )

prop_SatAtom = sat m1 (Atom "a") == S.fromList [1]
prop_SatNot = sat m1 (CNot $ Atom "a") == S.fromList [2,3]
prop_SatAX = sat m2 (AX $ Atom "a") == S.fromList [2,3,4]
prop_SatEX = sat m3 (EX $ Atom "a") == S.fromList [2,3]
prop_SatEU = sat m4 (EU (Atom "a") (Atom "b")) == S.fromList [1,2,3]
prop_SatAU = sat m4 (AU (Atom "a") (Atom "b")) == S.fromList [3]
prop_SatEF = sat m4 (EF (Atom "b")) == S.fromList [1,2,3]
prop_SatEG = sat m4 (EG (Atom "b")) == S.fromList [1,2,3]
prop_SatAF = sat m4 (AF (Atom "b")) == S.fromList [3]
prop_SatAG = sat m4 (AG (Atom "b")) == S.fromList [3]
prop_SatAU' = sat m4 (AU (Atom "a") (Atom "b")) == S.fromList [3,2]

runTests = $quickCheckAll

