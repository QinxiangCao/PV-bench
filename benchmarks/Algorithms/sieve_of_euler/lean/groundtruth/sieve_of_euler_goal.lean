import SimpleC.SL.SeparationLogic

import Algorithms.sieve_of_euler.lean.helper_lib
open scoped SimpleC

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace Algorithms.sieve_of_euler.lean.groundtruth.sieve_of_euler_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC

local instance sieve_of_euler_goalSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray

noncomputable def get_prime_safety_wit_1 : Prop :=
  forall (prime_pre : Int) (flag_pre : Int) (tot_pre : Int) (n_pre : Int) (prime0 : (List Int)) (flag0 : (List Int)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : ((Zlength (flag0)) = (n_pre - 1))) (PreH4 : ((Zlength (prime0)) = n_pre)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "tot" ) )) # Int |-> (tot_pre))
  ** ((( &( "flag" ) )) # Ptr |-> (flag_pre))
  ** ((( &( "prime" ) )) # Ptr |-> (prime_pre))
  ** (intArray.seg flag_pre 2 (n_pre + 1) flag0)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime0)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def get_prime_safety_wit_2 : Prop :=
  forall (prime_pre : Int) (flag_pre : Int) (n_pre : Int) (prime0 : (List Int)) (flag0 : (List Int)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : ((Zlength (flag0)) = (n_pre - 1))) (PreH4 : ((Zlength (prime0)) = n_pre)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "tot" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "flag" ) )) # Ptr |-> (flag_pre))
  ** ((( &( "prime" ) )) # Ptr |-> (prime_pre))
  ** (intArray.seg flag_pre 2 (n_pre + 1) flag0)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime0)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def get_prime_safety_wit_3 : Prop :=
  forall (prime_pre : Int) (flag_pre : Int) (n_pre : Int) (prime0 : (List Int)) (flag_l : (List Int)) (i : Int) (tot : Int) (PreH1 : (i <= n_pre)) (PreH2 : (tot = (0 : Int))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : (EulerInitPrefix n_pre i flag_l)) ,
  (intArray.seg flag_pre 2 (n_pre + 1) (replace_Znth ((i - 2)) (i) (flag_l)))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "flag" ) )) # Ptr |-> (flag_pre))
  ** ((( &( "prime" ) )) # Ptr |-> (prime_pre))
  ** ((( &( "tot" ) )) # Int |-> (tot))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime0)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def get_prime_safety_wit_4 : Prop :=
  forall (prime_pre : Int) (flag_pre : Int) (n_pre : Int) (prime0 : (List Int)) (flag_l : (List Int)) (tot : Int) (PreH1 : (tot = (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (EulerOuterState n_pre 2 tot flag_l prime0)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "flag" ) )) # Ptr |-> (flag_pre))
  ** ((( &( "prime" ) )) # Ptr |-> (prime_pre))
  ** ((( &( "tot" ) )) # Int |-> (tot))
  ** (intArray.seg flag_pre 2 (n_pre + 1) flag_l)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime0)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def get_prime_safety_wit_5 : Prop :=
  forall (prime_pre : Int) (flag_pre : Int) (n_pre : Int) (flag_l : (List Int)) (prime_l : (List Int)) (tot : Int) (i : Int) (PreH1 : ((Znth (i - 2) flag_l (0 : Int)) = i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : ((0 : Int) <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l prime_l)) ,
  (intArray.seg flag_pre 2 (n_pre + 1) flag_l)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "flag" ) )) # Ptr |-> (flag_pre))
  ** ((( &( "prime" ) )) # Ptr |-> (prime_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "tot" ) )) # Int |-> (tot))
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime_l)
|--
  “ ((tot + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (tot + 1)) ”

noncomputable def get_prime_safety_wit_6 : Prop :=
  forall (prime_pre : Int) (flag_pre : Int) (n_pre : Int) (flag_l : (List Int)) (prime_l : (List Int)) (tot : Int) (i : Int) (PreH1 : ((Znth (i - 2) flag_l (0 : Int)) = i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : ((0 : Int) <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l prime_l)) ,
  (intArray.seg flag_pre 2 (n_pre + 1) flag_l)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "flag" ) )) # Ptr |-> (flag_pre))
  ** ((( &( "prime" ) )) # Ptr |-> (prime_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "tot" ) )) # Int |-> (tot))
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime_l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def get_prime_safety_wit_7 : Prop :=
  forall (prime_pre : Int) (flag_pre : Int) (n_pre : Int) (flag_l : (List Int)) (prime_l : (List Int)) (i : Int) (tot : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (2 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (1 <= tot)) (PreH6 : (tot <= n_pre)) (PreH7 : (EulerInnerState n_pre i 1 tot flag_l prime_l)) (PreH8 : (2 <= (Znth (0 : Int) prime_l (0 : Int)))) (PreH9 : ((Znth (0 : Int) prime_l (0 : Int)) <= i)) (PreH10 : ((i * (Znth (0 : Int) prime_l (0 : Int))) <= INT_MAX)) ,
  ((( &( "j" ) )) # Int |->_)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "flag" ) )) # Ptr |-> (flag_pre))
  ** ((( &( "prime" ) )) # Ptr |-> (prime_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "tot" ) )) # Int |-> (tot))
  ** (intArray.seg flag_pre 2 (n_pre + 1) flag_l)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime_l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def get_prime_safety_wit_8 : Prop :=
  forall (prime_pre : Int) (flag_pre : Int) (n_pre : Int) (flag_l : (List Int)) (prime_l : (List Int)) (j : Int) (tot : Int) (i : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (2 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (1 <= tot)) (PreH6 : (tot <= n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= tot)) (PreH9 : (EulerInnerState n_pre i j tot flag_l prime_l)) (PreH10 : (2 <= (Znth (j - 1) prime_l (0 : Int)))) (PreH11 : ((Znth (j - 1) prime_l (0 : Int)) <= i)) (PreH12 : ((i * (Znth (j - 1) prime_l (0 : Int))) <= INT_MAX)) ,
  (intArray.seg prime_pre 1 (n_pre + 1) prime_l)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "flag" ) )) # Ptr |-> (flag_pre))
  ** ((( &( "prime" ) )) # Ptr |-> (prime_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "tot" ) )) # Int |-> (tot))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.seg flag_pre 2 (n_pre + 1) flag_l)
|--
  “ ((i * (Znth (j - 1) prime_l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i * (Znth (j - 1) prime_l (0 : Int)))) ”

noncomputable def get_prime_safety_wit_9 : Prop :=
  forall (prime_pre : Int) (flag_pre : Int) (n_pre : Int) (flag_l : (List Int)) (prime_l : (List Int)) (j : Int) (tot : Int) (i : Int) (PreH1 : (j > tot)) (PreH2 : ((i * (Znth (j - 1) prime_l (0 : Int))) <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (1 <= tot)) (PreH8 : (tot <= n_pre)) (PreH9 : (1 <= j)) (PreH10 : (j <= tot)) (PreH11 : (EulerInnerState n_pre i j tot flag_l prime_l)) (PreH12 : (2 <= (Znth (j - 1) prime_l (0 : Int)))) (PreH13 : ((Znth (j - 1) prime_l (0 : Int)) <= i)) (PreH14 : ((i * (Znth (j - 1) prime_l (0 : Int))) <= INT_MAX)) ,
  (intArray.seg prime_pre 1 (n_pre + 1) prime_l)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "flag" ) )) # Ptr |-> (flag_pre))
  ** ((( &( "prime" ) )) # Ptr |-> (prime_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "tot" ) )) # Int |-> (tot))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.seg flag_pre 2 (n_pre + 1) flag_l)
|--
  “ False ”

noncomputable def get_prime_safety_wit_10 : Prop :=
  forall (prime_pre : Int) (flag_pre : Int) (n_pre : Int) (flag_l : (List Int)) (prime_l : (List Int)) (j : Int) (tot : Int) (i : Int) (PreH1 : (j <= tot)) (PreH2 : ((i * (Znth (j - 1) prime_l (0 : Int))) <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (1 <= tot)) (PreH8 : (tot <= n_pre)) (PreH9 : (1 <= j)) (PreH10 : (j <= tot)) (PreH11 : (EulerInnerState n_pre i j tot flag_l prime_l)) (PreH12 : (2 <= (Znth (j - 1) prime_l (0 : Int)))) (PreH13 : ((Znth (j - 1) prime_l (0 : Int)) <= i)) (PreH14 : ((i * (Znth (j - 1) prime_l (0 : Int))) <= INT_MAX)) ,
  (intArray.seg prime_pre 1 (n_pre + 1) prime_l)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "flag" ) )) # Ptr |-> (flag_pre))
  ** ((( &( "prime" ) )) # Ptr |-> (prime_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "tot" ) )) # Int |-> (tot))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.seg flag_pre 2 (n_pre + 1) flag_l)
|--
  “ ((i * (Znth (j - 1) prime_l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i * (Znth (j - 1) prime_l (0 : Int)))) ”

noncomputable def get_prime_safety_wit_11 : Prop :=
  forall (prime_pre : Int) (flag_pre : Int) (n_pre : Int) (flag_l : (List Int)) (prime_l : (List Int)) (i : Int) (tot : Int) (j : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (2 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (1 <= tot)) (PreH6 : (tot <= n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= tot)) (PreH9 : ((i * (Znth (j - 1) prime_l (0 : Int))) <= n_pre)) (PreH10 : (EulerInnerMarkedState n_pre i j tot flag_l prime_l)) (PreH11 : (2 <= (Znth (j - 1) prime_l (0 : Int)))) (PreH12 : ((Znth (j - 1) prime_l (0 : Int)) <= i)) ,
  (intArray.seg prime_pre 1 (n_pre + 1) prime_l)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "flag" ) )) # Ptr |-> (flag_pre))
  ** ((( &( "prime" ) )) # Ptr |-> (prime_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "tot" ) )) # Int |-> (tot))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.seg flag_pre 2 (n_pre + 1) flag_l)
|--
  “ ((i ≠ (INT_MIN)) ∨ ((Znth (j - 1) prime_l (0 : Int)) ≠ (-1))) ” &&
  “ ((Znth (j - 1) prime_l (0 : Int)) ≠ (0 : Int)) ”

noncomputable def get_prime_safety_wit_12 : Prop :=
  forall (prime_pre : Int) (flag_pre : Int) (n_pre : Int) (flag_l : (List Int)) (prime_l : (List Int)) (i : Int) (tot : Int) (j : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (2 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (1 <= tot)) (PreH6 : (tot <= n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= tot)) (PreH9 : ((i * (Znth (j - 1) prime_l (0 : Int))) <= n_pre)) (PreH10 : (EulerInnerMarkedState n_pre i j tot flag_l prime_l)) (PreH11 : (2 <= (Znth (j - 1) prime_l (0 : Int)))) (PreH12 : ((Znth (j - 1) prime_l (0 : Int)) <= i)) ,
  (intArray.seg prime_pre 1 (n_pre + 1) prime_l)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "flag" ) )) # Ptr |-> (flag_pre))
  ** ((( &( "prime" ) )) # Ptr |-> (prime_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "tot" ) )) # Int |-> (tot))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.seg flag_pre 2 (n_pre + 1) flag_l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def get_prime_safety_wit_13 : Prop :=
  forall (prime_pre : Int) (flag_pre : Int) (n_pre : Int) (flag_l : (List Int)) (prime_l : (List Int)) (i : Int) (tot : Int) (j : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (2 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (1 <= tot)) (PreH6 : (tot <= n_pre)) (PreH7 : (1 <= (j + 1))) (PreH8 : ((j + 1) <= tot)) (PreH9 : (EulerInnerState n_pre i (j + 1) tot flag_l prime_l)) (PreH10 : (2 <= (Znth j prime_l (0 : Int)))) (PreH11 : ((Znth j prime_l (0 : Int)) <= i)) (PreH12 : ((i * (Znth j prime_l (0 : Int))) <= INT_MAX)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "flag" ) )) # Ptr |-> (flag_pre))
  ** ((( &( "prime" ) )) # Ptr |-> (prime_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "tot" ) )) # Int |-> (tot))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.seg flag_pre 2 (n_pre + 1) flag_l)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime_l)
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def get_prime_safety_wit_14 : Prop :=
  forall (prime_pre : Int) (flag_pre : Int) (n_pre : Int) (flag_l : (List Int)) (prime_l : (List Int)) (i : Int) (tot : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (2 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : ((0 : Int) <= tot)) (PreH6 : (tot < (i + 1))) (PreH7 : (EulerOuterState n_pre (i + 1) tot flag_l prime_l)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "flag" ) )) # Ptr |-> (flag_pre))
  ** ((( &( "prime" ) )) # Ptr |-> (prime_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "tot" ) )) # Int |-> (tot))
  ** (intArray.seg flag_pre 2 (n_pre + 1) flag_l)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime_l)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def get_prime_entail_wit_1 : Prop :=
  (
forall (prime_pre : Int) (flag_pre : Int) (n_pre : Int) (prime0 : (List Int)) (flag0 : (List Int)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : ((Zlength (flag0)) = (n_pre - 1))) (PreH4 : ((Zlength (prime0)) = n_pre)) ,
  (intArray.seg flag_pre 2 (n_pre + 1) flag0)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime0)
|--
  EX flag_l : (List Int),
  “ ((0 : Int) = (0 : Int)) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 46340) ” &&
  “ (2 <= 2) ” &&
  “ (2 <= (n_pre + 1)) ” &&
  “ (EulerInitPrefix n_pre 2 flag_l) ”
  &&  (intArray.seg flag_pre 2 (n_pre + 1) flag_l)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime0)
) \/
(
forall (n_pre : Int) (prime0 : (List Int)) (flag0 : (List Int)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : ((Zlength (flag0)) = (n_pre - 1))) (PreH4 : ((Zlength (prime0)) = n_pre)) ,
  TT && emp 
|--
  “ (EulerInitPrefix n_pre 2 flag0) ”
  &&  emp
)

noncomputable def get_prime_entail_wit_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (prime0 : (List Int)) (flag0 : (List Int)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : ((Zlength (flag0)) = (n_pre - 1))) (PreH4 : ((Zlength (prime0)) = n_pre)) ,
  (EulerInitPrefix n_pre 2 flag0)

noncomputable def get_prime_entail_wit_2 : Prop :=
  (
forall (prime_pre : Int) (flag_pre : Int) (n_pre : Int) (prime0 : (List Int)) (flag_l_2 : (List Int)) (i : Int) (tot : Int) (PreH1 : (i <= n_pre)) (PreH2 : (tot = (0 : Int))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : (EulerInitPrefix n_pre i flag_l_2)) ,
  (intArray.seg flag_pre 2 (n_pre + 1) (replace_Znth ((i - 2)) (i) (flag_l_2)))
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime0)
|--
  EX flag_l : (List Int),
  “ (tot = (0 : Int)) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 46340) ” &&
  “ (2 <= (i + 1)) ” &&
  “ ((i + 1) <= (n_pre + 1)) ” &&
  “ (EulerInitPrefix n_pre (i + 1) flag_l) ”
  &&  (intArray.seg flag_pre 2 (n_pre + 1) flag_l)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime0)
) \/
(
forall (n_pre : Int) (flag_l_2 : (List Int)) (i : Int) (tot : Int) (PreH1 : (i <= n_pre)) (PreH2 : (tot = (0 : Int))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : (EulerInitPrefix n_pre i flag_l_2)) ,
  TT && emp 
|--
  “ (EulerInitPrefix n_pre (i + 1) (replace_Znth ((i - 2)) (i) (flag_l_2))) ”
  &&  emp
)

noncomputable def get_prime_entail_wit_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (flag_l_2 : (List Int)) (i : Int) (tot : Int) (PreH1 : (i <= n_pre)) (PreH2 : (tot = (0 : Int))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : (EulerInitPrefix n_pre i flag_l_2)) ,
  (EulerInitPrefix n_pre (i + 1) (replace_Znth ((i - 2)) (i) (flag_l_2)))

noncomputable def get_prime_entail_wit_3 : Prop :=
  (
forall (prime_pre : Int) (flag_pre : Int) (n_pre : Int) (prime0 : (List Int)) (flag_l_2 : (List Int)) (i : Int) (tot : Int) (PreH1 : (i > n_pre)) (PreH2 : (tot = (0 : Int))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : (EulerInitPrefix n_pre i flag_l_2)) ,
  (intArray.seg flag_pre 2 (n_pre + 1) flag_l_2)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime0)
|--
  EX flag_l : (List Int),
  “ (tot = (0 : Int)) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 46340) ” &&
  “ (EulerOuterState n_pre 2 tot flag_l prime0) ”
  &&  (intArray.seg flag_pre 2 (n_pre + 1) flag_l)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime0)
) \/
(
forall (n_pre : Int) (prime0 : (List Int)) (flag_l_2 : (List Int)) (i : Int) (tot : Int) (PreH1 : (i > n_pre)) (PreH2 : (tot = (0 : Int))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : (EulerInitPrefix n_pre i flag_l_2)) ,
  TT && emp 
|--
  “ (EulerOuterState n_pre 2 (0 : Int) flag_l_2 prime0) ”
  &&  emp
)

noncomputable def get_prime_entail_wit_3_split_goal_1 : Prop :=
  forall (n_pre : Int) (prime0 : (List Int)) (flag_l_2 : (List Int)) (i : Int) (tot : Int) (PreH1 : (i > n_pre)) (PreH2 : (tot = (0 : Int))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : (EulerInitPrefix n_pre i flag_l_2)) ,
  (EulerOuterState n_pre 2 (0 : Int) flag_l_2 prime0)

noncomputable def get_prime_entail_wit_4 : Prop :=
  forall (prime_pre : Int) (flag_pre : Int) (n_pre : Int) (prime0 : (List Int)) (flag_l_2 : (List Int)) (tot : Int) (PreH1 : (tot = (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (EulerOuterState n_pre 2 tot flag_l_2 prime0)) ,
  (intArray.seg flag_pre 2 (n_pre + 1) flag_l_2)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime0)
|--
  EX flag_l : (List Int), EX prime_l : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 46340) ” &&
  “ (2 <= 2) ” &&
  “ (2 <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= tot) ” &&
  “ (tot < 2) ” &&
  “ (EulerOuterState n_pre 2 tot flag_l prime_l) ”
  &&  (intArray.seg flag_pre 2 (n_pre + 1) flag_l)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime_l)

noncomputable def get_prime_entail_wit_5_1 : Prop :=
  (
forall (prime_pre : Int) (flag_pre : Int) (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (tot : Int) (i : Int) (PreH1 : ((Znth (i - 2) flag_l_2 (0 : Int)) = i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : ((0 : Int) <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l_2 prime_l_2)) ,
  (intArray.seg prime_pre 1 (n_pre + 1) (replace_Znth (((tot + 1) - 1)) (i) (prime_l_2)))
  ** (intArray.seg flag_pre 2 (n_pre + 1) flag_l_2)
|--
  EX flag_l : (List Int), EX prime_l : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 46340) ” &&
  “ (2 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= (tot + 1)) ” &&
  “ ((tot + 1) <= n_pre) ” &&
  “ (EulerInnerState n_pre i 1 (tot + 1) flag_l prime_l) ” &&
  “ (2 <= (Znth (0 : Int) prime_l (0 : Int))) ” &&
  “ ((Znth (0 : Int) prime_l (0 : Int)) <= i) ” &&
  “ ((i * (Znth (0 : Int) prime_l (0 : Int))) <= INT_MAX) ”
  &&  (intArray.seg flag_pre 2 (n_pre + 1) flag_l)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime_l)
) \/
(
forall (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (tot : Int) (i : Int) (PreH1 : ((Znth (i - 2) flag_l_2 (0 : Int)) = i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : ((0 : Int) <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l_2 prime_l_2)) ,
  TT && emp 
|--
  “ ((i * (Znth (0 : Int) (replace_Znth (((tot + 1) - 1)) (i) (prime_l_2)) (0 : Int))) <= INT_MAX) ” &&
  “ ((Znth (0 : Int) (replace_Znth (((tot + 1) - 1)) (i) (prime_l_2)) (0 : Int)) <= i) ” &&
  “ (2 <= (Znth (0 : Int) (replace_Znth (((tot + 1) - 1)) (i) (prime_l_2)) (0 : Int))) ” &&
  “ (EulerInnerState n_pre i 1 (tot + 1) flag_l_2 (replace_Znth (((tot + 1) - 1)) (i) (prime_l_2))) ”
  &&  emp
)

noncomputable def get_prime_entail_wit_5_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (tot : Int) (i : Int) (PreH1 : ((Znth (i - 2) flag_l_2 (0 : Int)) = i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : ((0 : Int) <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l_2 prime_l_2)) ,
  ((i * (Znth (0 : Int) (replace_Znth (((tot + 1) - 1)) (i) (prime_l_2)) (0 : Int))) <= INT_MAX)

noncomputable def get_prime_entail_wit_5_1_split_goal_2 : Prop :=
  forall (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (tot : Int) (i : Int) (PreH1 : ((Znth (i - 2) flag_l_2 (0 : Int)) = i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : ((0 : Int) <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l_2 prime_l_2)) ,
  ((Znth (0 : Int) (replace_Znth (((tot + 1) - 1)) (i) (prime_l_2)) (0 : Int)) <= i)

noncomputable def get_prime_entail_wit_5_1_split_goal_3 : Prop :=
  forall (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (tot : Int) (i : Int) (PreH1 : ((Znth (i - 2) flag_l_2 (0 : Int)) = i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : ((0 : Int) <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l_2 prime_l_2)) ,
  (2 <= (Znth (0 : Int) (replace_Znth (((tot + 1) - 1)) (i) (prime_l_2)) (0 : Int)))

noncomputable def get_prime_entail_wit_5_1_split_goal_4 : Prop :=
  forall (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (tot : Int) (i : Int) (PreH1 : ((Znth (i - 2) flag_l_2 (0 : Int)) = i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : ((0 : Int) <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l_2 prime_l_2)) ,
  (EulerInnerState n_pre i 1 (tot + 1) flag_l_2 (replace_Znth (((tot + 1) - 1)) (i) (prime_l_2)))

noncomputable def get_prime_entail_wit_5_2 : Prop :=
  (
forall (prime_pre : Int) (flag_pre : Int) (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (tot : Int) (i : Int) (PreH1 : ((Znth (i - 2) flag_l_2 (0 : Int)) ≠ i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : ((0 : Int) <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l_2 prime_l_2)) ,
  (intArray.seg flag_pre 2 (n_pre + 1) flag_l_2)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime_l_2)
|--
  EX flag_l : (List Int), EX prime_l : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 46340) ” &&
  “ (2 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= tot) ” &&
  “ (tot <= n_pre) ” &&
  “ (EulerInnerState n_pre i 1 tot flag_l prime_l) ” &&
  “ (2 <= (Znth (0 : Int) prime_l (0 : Int))) ” &&
  “ ((Znth (0 : Int) prime_l (0 : Int)) <= i) ” &&
  “ ((i * (Znth (0 : Int) prime_l (0 : Int))) <= INT_MAX) ”
  &&  (intArray.seg flag_pre 2 (n_pre + 1) flag_l)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime_l)
) \/
(
forall (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (tot : Int) (i : Int) (PreH1 : ((Znth (i - 2) flag_l_2 (0 : Int)) ≠ i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : ((0 : Int) <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l_2 prime_l_2)) ,
  TT && emp 
|--
  “ ((i * (Znth (0 : Int) prime_l_2 (0 : Int))) <= INT_MAX) ” &&
  “ ((Znth (0 : Int) prime_l_2 (0 : Int)) <= i) ” &&
  “ (2 <= (Znth (0 : Int) prime_l_2 (0 : Int))) ” &&
  “ (EulerInnerState n_pre i 1 tot flag_l_2 prime_l_2) ” &&
  “ (1 <= tot) ”
  &&  emp
)

noncomputable def get_prime_entail_wit_5_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (tot : Int) (i : Int) (PreH1 : ((Znth (i - 2) flag_l_2 (0 : Int)) ≠ i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : ((0 : Int) <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l_2 prime_l_2)) ,
  ((i * (Znth (0 : Int) prime_l_2 (0 : Int))) <= INT_MAX)

noncomputable def get_prime_entail_wit_5_2_split_goal_2 : Prop :=
  forall (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (tot : Int) (i : Int) (PreH1 : ((Znth (i - 2) flag_l_2 (0 : Int)) ≠ i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : ((0 : Int) <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l_2 prime_l_2)) ,
  ((Znth (0 : Int) prime_l_2 (0 : Int)) <= i)

noncomputable def get_prime_entail_wit_5_2_split_goal_3 : Prop :=
  forall (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (tot : Int) (i : Int) (PreH1 : ((Znth (i - 2) flag_l_2 (0 : Int)) ≠ i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : ((0 : Int) <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l_2 prime_l_2)) ,
  (2 <= (Znth (0 : Int) prime_l_2 (0 : Int)))

noncomputable def get_prime_entail_wit_5_2_split_goal_4 : Prop :=
  forall (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (tot : Int) (i : Int) (PreH1 : ((Znth (i - 2) flag_l_2 (0 : Int)) ≠ i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : ((0 : Int) <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l_2 prime_l_2)) ,
  (EulerInnerState n_pre i 1 tot flag_l_2 prime_l_2)

noncomputable def get_prime_entail_wit_5_2_split_goal_5 : Prop :=
  forall (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (tot : Int) (i : Int) (PreH1 : ((Znth (i - 2) flag_l_2 (0 : Int)) ≠ i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : ((0 : Int) <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l_2 prime_l_2)) ,
  (1 <= tot)

noncomputable def get_prime_entail_wit_6 : Prop :=
  forall (prime_pre : Int) (flag_pre : Int) (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (i : Int) (tot : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (2 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (1 <= tot)) (PreH6 : (tot <= n_pre)) (PreH7 : (EulerInnerState n_pre i 1 tot flag_l_2 prime_l_2)) (PreH8 : (2 <= (Znth (0 : Int) prime_l_2 (0 : Int)))) (PreH9 : ((Znth (0 : Int) prime_l_2 (0 : Int)) <= i)) (PreH10 : ((i * (Znth (0 : Int) prime_l_2 (0 : Int))) <= INT_MAX)) ,
  (intArray.seg flag_pre 2 (n_pre + 1) flag_l_2)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime_l_2)
|--
  EX flag_l : (List Int), EX prime_l : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 46340) ” &&
  “ (2 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= tot) ” &&
  “ (tot <= n_pre) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= tot) ” &&
  “ (EulerInnerState n_pre i 1 tot flag_l prime_l) ” &&
  “ (2 <= (Znth (1 - 1) prime_l (0 : Int))) ” &&
  “ ((Znth (1 - 1) prime_l (0 : Int)) <= i) ” &&
  “ ((i * (Znth (1 - 1) prime_l (0 : Int))) <= INT_MAX) ”
  &&  (intArray.seg flag_pre 2 (n_pre + 1) flag_l)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime_l)

noncomputable def get_prime_entail_wit_7 : Prop :=
  (
forall (prime_pre : Int) (flag_pre : Int) (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (j : Int) (tot : Int) (i : Int) (PreH1 : (j <= tot)) (PreH2 : ((i * (Znth (j - 1) prime_l_2 (0 : Int))) <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (1 <= tot)) (PreH8 : (tot <= n_pre)) (PreH9 : (1 <= j)) (PreH10 : (j <= tot)) (PreH11 : (EulerInnerState n_pre i j tot flag_l_2 prime_l_2)) (PreH12 : (2 <= (Znth (j - 1) prime_l_2 (0 : Int)))) (PreH13 : ((Znth (j - 1) prime_l_2 (0 : Int)) <= i)) (PreH14 : ((i * (Znth (j - 1) prime_l_2 (0 : Int))) <= INT_MAX)) ,
  (intArray.seg flag_pre 2 (n_pre + 1) (replace_Znth (((i * (Znth (j - 1) prime_l_2 (0 : Int))) - 2)) ((Znth (j - 1) prime_l_2 (0 : Int))) (flag_l_2)))
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime_l_2)
|--
  EX flag_l : (List Int), EX prime_l : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 46340) ” &&
  “ (2 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= tot) ” &&
  “ (tot <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= tot) ” &&
  “ ((i * (Znth (j - 1) prime_l (0 : Int))) <= n_pre) ” &&
  “ (EulerInnerMarkedState n_pre i j tot flag_l prime_l) ” &&
  “ (2 <= (Znth (j - 1) prime_l (0 : Int))) ” &&
  “ ((Znth (j - 1) prime_l (0 : Int)) <= i) ”
  &&  (intArray.seg flag_pre 2 (n_pre + 1) flag_l)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime_l)
) \/
(
forall (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (j : Int) (tot : Int) (i : Int) (PreH1 : (j <= tot)) (PreH2 : ((i * (Znth (j - 1) prime_l_2 (0 : Int))) <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (1 <= tot)) (PreH8 : (tot <= n_pre)) (PreH9 : (1 <= j)) (PreH10 : (j <= tot)) (PreH11 : (EulerInnerState n_pre i j tot flag_l_2 prime_l_2)) (PreH12 : (2 <= (Znth (j - 1) prime_l_2 (0 : Int)))) (PreH13 : ((Znth (j - 1) prime_l_2 (0 : Int)) <= i)) (PreH14 : ((i * (Znth (j - 1) prime_l_2 (0 : Int))) <= INT_MAX)) ,
  TT && emp 
|--
  “ (EulerInnerMarkedState n_pre i j tot (replace_Znth (((i * (Znth (j - 1) prime_l_2 (0 : Int))) - 2)) ((Znth (j - 1) prime_l_2 (0 : Int))) (flag_l_2)) prime_l_2) ”
  &&  emp
)

noncomputable def get_prime_entail_wit_7_split_goal_1 : Prop :=
  forall (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (j : Int) (tot : Int) (i : Int) (PreH1 : (j <= tot)) (PreH2 : ((i * (Znth (j - 1) prime_l_2 (0 : Int))) <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (1 <= tot)) (PreH8 : (tot <= n_pre)) (PreH9 : (1 <= j)) (PreH10 : (j <= tot)) (PreH11 : (EulerInnerState n_pre i j tot flag_l_2 prime_l_2)) (PreH12 : (2 <= (Znth (j - 1) prime_l_2 (0 : Int)))) (PreH13 : ((Znth (j - 1) prime_l_2 (0 : Int)) <= i)) (PreH14 : ((i * (Znth (j - 1) prime_l_2 (0 : Int))) <= INT_MAX)) ,
  (EulerInnerMarkedState n_pre i j tot (replace_Znth (((i * (Znth (j - 1) prime_l_2 (0 : Int))) - 2)) ((Znth (j - 1) prime_l_2 (0 : Int))) (flag_l_2)) prime_l_2)

noncomputable def get_prime_entail_wit_8 : Prop :=
  (
forall (prime_pre : Int) (flag_pre : Int) (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (i : Int) (tot : Int) (j : Int) (PreH1 : ((Z.rem i (Znth (j - 1) prime_l_2 (0 : Int))) = (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (1 <= tot)) (PreH7 : (tot <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= tot)) (PreH10 : ((i * (Znth (j - 1) prime_l_2 (0 : Int))) <= n_pre)) (PreH11 : (EulerInnerMarkedState n_pre i j tot flag_l_2 prime_l_2)) (PreH12 : (2 <= (Znth (j - 1) prime_l_2 (0 : Int)))) (PreH13 : ((Znth (j - 1) prime_l_2 (0 : Int)) <= i)) ,
  (intArray.seg prime_pre 1 (n_pre + 1) prime_l_2)
  ** (intArray.seg flag_pre 2 (n_pre + 1) flag_l_2)
|--
  EX flag_l : (List Int), EX prime_l : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 46340) ” &&
  “ (2 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= tot) ” &&
  “ (tot <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= tot) ” &&
  “ (2 <= (Znth (j - 1) prime_l (0 : Int))) ” &&
  “ ((Znth (j - 1) prime_l (0 : Int)) <= i) ” &&
  “ (EulerOuterState n_pre (i + 1) tot flag_l prime_l) ”
  &&  (intArray.seg flag_pre 2 (n_pre + 1) flag_l)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime_l)
) \/
(
forall (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (i : Int) (tot : Int) (j : Int) (PreH1 : ((Z.rem i (Znth (j - 1) prime_l_2 (0 : Int))) = (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (1 <= tot)) (PreH7 : (tot <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= tot)) (PreH10 : ((i * (Znth (j - 1) prime_l_2 (0 : Int))) <= n_pre)) (PreH11 : (EulerInnerMarkedState n_pre i j tot flag_l_2 prime_l_2)) (PreH12 : (2 <= (Znth (j - 1) prime_l_2 (0 : Int)))) (PreH13 : ((Znth (j - 1) prime_l_2 (0 : Int)) <= i)) ,
  TT && emp 
|--
  “ (EulerOuterState n_pre (i + 1) tot flag_l_2 prime_l_2) ”
  &&  emp
)

noncomputable def get_prime_entail_wit_8_split_goal_1 : Prop :=
  forall (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (i : Int) (tot : Int) (j : Int) (PreH1 : ((Z.rem i (Znth (j - 1) prime_l_2 (0 : Int))) = (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (1 <= tot)) (PreH7 : (tot <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= tot)) (PreH10 : ((i * (Znth (j - 1) prime_l_2 (0 : Int))) <= n_pre)) (PreH11 : (EulerInnerMarkedState n_pre i j tot flag_l_2 prime_l_2)) (PreH12 : (2 <= (Znth (j - 1) prime_l_2 (0 : Int)))) (PreH13 : ((Znth (j - 1) prime_l_2 (0 : Int)) <= i)) ,
  (EulerOuterState n_pre (i + 1) tot flag_l_2 prime_l_2)

noncomputable def get_prime_entail_wit_9 : Prop :=
  (
forall (prime_pre : Int) (flag_pre : Int) (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (i : Int) (tot : Int) (j : Int) (PreH1 : ((Z.rem i (Znth (j - 1) prime_l_2 (0 : Int))) ≠ (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (1 <= tot)) (PreH7 : (tot <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= tot)) (PreH10 : ((i * (Znth (j - 1) prime_l_2 (0 : Int))) <= n_pre)) (PreH11 : (EulerInnerMarkedState n_pre i j tot flag_l_2 prime_l_2)) (PreH12 : (2 <= (Znth (j - 1) prime_l_2 (0 : Int)))) (PreH13 : ((Znth (j - 1) prime_l_2 (0 : Int)) <= i)) ,
  (intArray.seg prime_pre 1 (n_pre + 1) prime_l_2)
  ** (intArray.seg flag_pre 2 (n_pre + 1) flag_l_2)
|--
  EX flag_l : (List Int), EX prime_l : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 46340) ” &&
  “ (2 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= tot) ” &&
  “ (tot <= n_pre) ” &&
  “ (1 <= (j + 1)) ” &&
  “ ((j + 1) <= tot) ” &&
  “ (EulerInnerState n_pre i (j + 1) tot flag_l prime_l) ” &&
  “ (2 <= (Znth j prime_l (0 : Int))) ” &&
  “ ((Znth j prime_l (0 : Int)) <= i) ” &&
  “ ((i * (Znth j prime_l (0 : Int))) <= INT_MAX) ”
  &&  (intArray.seg flag_pre 2 (n_pre + 1) flag_l)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime_l)
) \/
(
forall (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (i : Int) (tot : Int) (j : Int) (PreH1 : ((Z.rem i (Znth (j - 1) prime_l_2 (0 : Int))) ≠ (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (1 <= tot)) (PreH7 : (tot <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= tot)) (PreH10 : ((i * (Znth (j - 1) prime_l_2 (0 : Int))) <= n_pre)) (PreH11 : (EulerInnerMarkedState n_pre i j tot flag_l_2 prime_l_2)) (PreH12 : (2 <= (Znth (j - 1) prime_l_2 (0 : Int)))) (PreH13 : ((Znth (j - 1) prime_l_2 (0 : Int)) <= i)) ,
  TT && emp 
|--
  “ ((i * (Znth j prime_l_2 (0 : Int))) <= INT_MAX) ” &&
  “ ((Znth j prime_l_2 (0 : Int)) <= i) ” &&
  “ (2 <= (Znth j prime_l_2 (0 : Int))) ” &&
  “ (EulerInnerState n_pre i (j + 1) tot flag_l_2 prime_l_2) ” &&
  “ ((j + 1) <= tot) ”
  &&  emp
)

noncomputable def get_prime_entail_wit_9_split_goal_1 : Prop :=
  forall (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (i : Int) (tot : Int) (j : Int) (PreH1 : ((Z.rem i (Znth (j - 1) prime_l_2 (0 : Int))) ≠ (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (1 <= tot)) (PreH7 : (tot <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= tot)) (PreH10 : ((i * (Znth (j - 1) prime_l_2 (0 : Int))) <= n_pre)) (PreH11 : (EulerInnerMarkedState n_pre i j tot flag_l_2 prime_l_2)) (PreH12 : (2 <= (Znth (j - 1) prime_l_2 (0 : Int)))) (PreH13 : ((Znth (j - 1) prime_l_2 (0 : Int)) <= i)) ,
  ((i * (Znth j prime_l_2 (0 : Int))) <= INT_MAX)

noncomputable def get_prime_entail_wit_9_split_goal_2 : Prop :=
  forall (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (i : Int) (tot : Int) (j : Int) (PreH1 : ((Z.rem i (Znth (j - 1) prime_l_2 (0 : Int))) ≠ (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (1 <= tot)) (PreH7 : (tot <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= tot)) (PreH10 : ((i * (Znth (j - 1) prime_l_2 (0 : Int))) <= n_pre)) (PreH11 : (EulerInnerMarkedState n_pre i j tot flag_l_2 prime_l_2)) (PreH12 : (2 <= (Znth (j - 1) prime_l_2 (0 : Int)))) (PreH13 : ((Znth (j - 1) prime_l_2 (0 : Int)) <= i)) ,
  ((Znth j prime_l_2 (0 : Int)) <= i)

noncomputable def get_prime_entail_wit_9_split_goal_3 : Prop :=
  forall (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (i : Int) (tot : Int) (j : Int) (PreH1 : ((Z.rem i (Znth (j - 1) prime_l_2 (0 : Int))) ≠ (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (1 <= tot)) (PreH7 : (tot <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= tot)) (PreH10 : ((i * (Znth (j - 1) prime_l_2 (0 : Int))) <= n_pre)) (PreH11 : (EulerInnerMarkedState n_pre i j tot flag_l_2 prime_l_2)) (PreH12 : (2 <= (Znth (j - 1) prime_l_2 (0 : Int)))) (PreH13 : ((Znth (j - 1) prime_l_2 (0 : Int)) <= i)) ,
  (2 <= (Znth j prime_l_2 (0 : Int)))

noncomputable def get_prime_entail_wit_9_split_goal_4 : Prop :=
  forall (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (i : Int) (tot : Int) (j : Int) (PreH1 : ((Z.rem i (Znth (j - 1) prime_l_2 (0 : Int))) ≠ (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (1 <= tot)) (PreH7 : (tot <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= tot)) (PreH10 : ((i * (Znth (j - 1) prime_l_2 (0 : Int))) <= n_pre)) (PreH11 : (EulerInnerMarkedState n_pre i j tot flag_l_2 prime_l_2)) (PreH12 : (2 <= (Znth (j - 1) prime_l_2 (0 : Int)))) (PreH13 : ((Znth (j - 1) prime_l_2 (0 : Int)) <= i)) ,
  (EulerInnerState n_pre i (j + 1) tot flag_l_2 prime_l_2)

noncomputable def get_prime_entail_wit_9_split_goal_5 : Prop :=
  forall (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (i : Int) (tot : Int) (j : Int) (PreH1 : ((Z.rem i (Znth (j - 1) prime_l_2 (0 : Int))) ≠ (0 : Int))) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (1 <= tot)) (PreH7 : (tot <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= tot)) (PreH10 : ((i * (Znth (j - 1) prime_l_2 (0 : Int))) <= n_pre)) (PreH11 : (EulerInnerMarkedState n_pre i j tot flag_l_2 prime_l_2)) (PreH12 : (2 <= (Znth (j - 1) prime_l_2 (0 : Int)))) (PreH13 : ((Znth (j - 1) prime_l_2 (0 : Int)) <= i)) ,
  ((j + 1) <= tot)

noncomputable def get_prime_entail_wit_10 : Prop :=
  (
forall (prime_pre : Int) (flag_pre : Int) (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (i : Int) (tot : Int) (j : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (2 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (1 <= tot)) (PreH6 : (tot <= n_pre)) (PreH7 : (1 <= (j + 1))) (PreH8 : ((j + 1) <= tot)) (PreH9 : (EulerInnerState n_pre i (j + 1) tot flag_l_2 prime_l_2)) (PreH10 : (2 <= (Znth j prime_l_2 (0 : Int)))) (PreH11 : ((Znth j prime_l_2 (0 : Int)) <= i)) (PreH12 : ((i * (Znth j prime_l_2 (0 : Int))) <= INT_MAX)) ,
  (intArray.seg flag_pre 2 (n_pre + 1) flag_l_2)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime_l_2)
|--
  EX flag_l : (List Int), EX prime_l : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 46340) ” &&
  “ (2 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= tot) ” &&
  “ (tot <= n_pre) ” &&
  “ (1 <= (j + 1)) ” &&
  “ ((j + 1) <= tot) ” &&
  “ (EulerInnerState n_pre i (j + 1) tot flag_l prime_l) ” &&
  “ (2 <= (Znth ((j + 1) - 1) prime_l (0 : Int))) ” &&
  “ ((Znth ((j + 1) - 1) prime_l (0 : Int)) <= i) ” &&
  “ ((i * (Znth ((j + 1) - 1) prime_l (0 : Int))) <= INT_MAX) ”
  &&  (intArray.seg flag_pre 2 (n_pre + 1) flag_l)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime_l)
) \/
(
forall (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (i : Int) (tot : Int) (j : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (2 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (1 <= tot)) (PreH6 : (tot <= n_pre)) (PreH7 : (1 <= (j + 1))) (PreH8 : ((j + 1) <= tot)) (PreH9 : (EulerInnerState n_pre i (j + 1) tot flag_l_2 prime_l_2)) (PreH10 : (2 <= (Znth j prime_l_2 (0 : Int)))) (PreH11 : ((Znth j prime_l_2 (0 : Int)) <= i)) (PreH12 : ((i * (Znth j prime_l_2 (0 : Int))) <= INT_MAX)) ,
  TT && emp 
|--
  “ ((i * (Znth ((j + 1) - 1) prime_l_2 (0 : Int))) <= INT_MAX) ” &&
  “ ((Znth ((j + 1) - 1) prime_l_2 (0 : Int)) <= i) ” &&
  “ (2 <= (Znth ((j + 1) - 1) prime_l_2 (0 : Int))) ”
  &&  emp
)

noncomputable def get_prime_entail_wit_10_split_goal_1 : Prop :=
  forall (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (i : Int) (tot : Int) (j : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (2 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (1 <= tot)) (PreH6 : (tot <= n_pre)) (PreH7 : (1 <= (j + 1))) (PreH8 : ((j + 1) <= tot)) (PreH9 : (EulerInnerState n_pre i (j + 1) tot flag_l_2 prime_l_2)) (PreH10 : (2 <= (Znth j prime_l_2 (0 : Int)))) (PreH11 : ((Znth j prime_l_2 (0 : Int)) <= i)) (PreH12 : ((i * (Znth j prime_l_2 (0 : Int))) <= INT_MAX)) ,
  ((i * (Znth ((j + 1) - 1) prime_l_2 (0 : Int))) <= INT_MAX)

noncomputable def get_prime_entail_wit_10_split_goal_2 : Prop :=
  forall (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (i : Int) (tot : Int) (j : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (2 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (1 <= tot)) (PreH6 : (tot <= n_pre)) (PreH7 : (1 <= (j + 1))) (PreH8 : ((j + 1) <= tot)) (PreH9 : (EulerInnerState n_pre i (j + 1) tot flag_l_2 prime_l_2)) (PreH10 : (2 <= (Znth j prime_l_2 (0 : Int)))) (PreH11 : ((Znth j prime_l_2 (0 : Int)) <= i)) (PreH12 : ((i * (Znth j prime_l_2 (0 : Int))) <= INT_MAX)) ,
  ((Znth ((j + 1) - 1) prime_l_2 (0 : Int)) <= i)

noncomputable def get_prime_entail_wit_10_split_goal_3 : Prop :=
  forall (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (i : Int) (tot : Int) (j : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (2 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (1 <= tot)) (PreH6 : (tot <= n_pre)) (PreH7 : (1 <= (j + 1))) (PreH8 : ((j + 1) <= tot)) (PreH9 : (EulerInnerState n_pre i (j + 1) tot flag_l_2 prime_l_2)) (PreH10 : (2 <= (Znth j prime_l_2 (0 : Int)))) (PreH11 : ((Znth j prime_l_2 (0 : Int)) <= i)) (PreH12 : ((i * (Znth j prime_l_2 (0 : Int))) <= INT_MAX)) ,
  (2 <= (Znth ((j + 1) - 1) prime_l_2 (0 : Int)))

noncomputable def get_prime_entail_wit_11_1 : Prop :=
  (
forall (prime_pre : Int) (flag_pre : Int) (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (j : Int) (tot : Int) (i : Int) (PreH1 : ((i * (Znth (j - 1) prime_l_2 (0 : Int))) > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (1 <= tot)) (PreH7 : (tot <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= tot)) (PreH10 : (EulerInnerState n_pre i j tot flag_l_2 prime_l_2)) (PreH11 : (2 <= (Znth (j - 1) prime_l_2 (0 : Int)))) (PreH12 : ((Znth (j - 1) prime_l_2 (0 : Int)) <= i)) (PreH13 : ((i * (Znth (j - 1) prime_l_2 (0 : Int))) <= INT_MAX)) ,
  (intArray.seg prime_pre 1 (n_pre + 1) prime_l_2)
  ** (intArray.seg flag_pre 2 (n_pre + 1) flag_l_2)
|--
  EX flag_l : (List Int), EX prime_l : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 46340) ” &&
  “ (2 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= tot) ” &&
  “ (tot < (i + 1)) ” &&
  “ (EulerOuterState n_pre (i + 1) tot flag_l prime_l) ”
  &&  (intArray.seg flag_pre 2 (n_pre + 1) flag_l)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime_l)
) \/
(
forall (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (j : Int) (tot : Int) (i : Int) (PreH1 : ((i * (Znth (j - 1) prime_l_2 (0 : Int))) > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (1 <= tot)) (PreH7 : (tot <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= tot)) (PreH10 : (EulerInnerState n_pre i j tot flag_l_2 prime_l_2)) (PreH11 : (2 <= (Znth (j - 1) prime_l_2 (0 : Int)))) (PreH12 : ((Znth (j - 1) prime_l_2 (0 : Int)) <= i)) (PreH13 : ((i * (Znth (j - 1) prime_l_2 (0 : Int))) <= INT_MAX)) ,
  TT && emp 
|--
  “ (EulerOuterState n_pre (i + 1) tot flag_l_2 prime_l_2) ” &&
  “ (tot < (i + 1)) ”
  &&  emp
)

noncomputable def get_prime_entail_wit_11_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (j : Int) (tot : Int) (i : Int) (PreH1 : ((i * (Znth (j - 1) prime_l_2 (0 : Int))) > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (1 <= tot)) (PreH7 : (tot <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= tot)) (PreH10 : (EulerInnerState n_pre i j tot flag_l_2 prime_l_2)) (PreH11 : (2 <= (Znth (j - 1) prime_l_2 (0 : Int)))) (PreH12 : ((Znth (j - 1) prime_l_2 (0 : Int)) <= i)) (PreH13 : ((i * (Znth (j - 1) prime_l_2 (0 : Int))) <= INT_MAX)) ,
  (EulerOuterState n_pre (i + 1) tot flag_l_2 prime_l_2)

noncomputable def get_prime_entail_wit_11_1_split_goal_2 : Prop :=
  forall (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (j : Int) (tot : Int) (i : Int) (PreH1 : ((i * (Znth (j - 1) prime_l_2 (0 : Int))) > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (1 <= tot)) (PreH7 : (tot <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= tot)) (PreH10 : (EulerInnerState n_pre i j tot flag_l_2 prime_l_2)) (PreH11 : (2 <= (Znth (j - 1) prime_l_2 (0 : Int)))) (PreH12 : ((Znth (j - 1) prime_l_2 (0 : Int)) <= i)) (PreH13 : ((i * (Znth (j - 1) prime_l_2 (0 : Int))) <= INT_MAX)) ,
  (tot < (i + 1))

noncomputable def get_prime_entail_wit_11_2 : Prop :=
  (
forall (prime_pre : Int) (flag_pre : Int) (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (i : Int) (tot : Int) (j : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (2 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (1 <= tot)) (PreH6 : (tot <= n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= tot)) (PreH9 : (2 <= (Znth (j - 1) prime_l_2 (0 : Int)))) (PreH10 : ((Znth (j - 1) prime_l_2 (0 : Int)) <= i)) (PreH11 : (EulerOuterState n_pre (i + 1) tot flag_l_2 prime_l_2)) ,
  (intArray.seg flag_pre 2 (n_pre + 1) flag_l_2)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime_l_2)
|--
  EX flag_l : (List Int), EX prime_l : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 46340) ” &&
  “ (2 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= tot) ” &&
  “ (tot < (i + 1)) ” &&
  “ (EulerOuterState n_pre (i + 1) tot flag_l prime_l) ”
  &&  (intArray.seg flag_pre 2 (n_pre + 1) flag_l)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime_l)
) \/
(
forall (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (i : Int) (tot : Int) (j : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (2 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (1 <= tot)) (PreH6 : (tot <= n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= tot)) (PreH9 : (2 <= (Znth (j - 1) prime_l_2 (0 : Int)))) (PreH10 : ((Znth (j - 1) prime_l_2 (0 : Int)) <= i)) (PreH11 : (EulerOuterState n_pre (i + 1) tot flag_l_2 prime_l_2)) ,
  TT && emp 
|--
  “ (tot < (i + 1)) ”
  &&  emp
)

noncomputable def get_prime_entail_wit_11_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (i : Int) (tot : Int) (j : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (2 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (1 <= tot)) (PreH6 : (tot <= n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= tot)) (PreH9 : (2 <= (Znth (j - 1) prime_l_2 (0 : Int)))) (PreH10 : ((Znth (j - 1) prime_l_2 (0 : Int)) <= i)) (PreH11 : (EulerOuterState n_pre (i + 1) tot flag_l_2 prime_l_2)) ,
  (tot < (i + 1))

noncomputable def get_prime_entail_wit_12 : Prop :=
  forall (prime_pre : Int) (flag_pre : Int) (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (i : Int) (tot : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (2 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : ((0 : Int) <= tot)) (PreH6 : (tot < (i + 1))) (PreH7 : (EulerOuterState n_pre (i + 1) tot flag_l_2 prime_l_2)) ,
  (intArray.seg flag_pre 2 (n_pre + 1) flag_l_2)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime_l_2)
|--
  EX flag_l : (List Int), EX prime_l : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 46340) ” &&
  “ (2 <= (i + 1)) ” &&
  “ ((i + 1) <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= tot) ” &&
  “ (tot < (i + 1)) ” &&
  “ (EulerOuterState n_pre (i + 1) tot flag_l prime_l) ”
  &&  (intArray.seg flag_pre 2 (n_pre + 1) flag_l)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime_l)

noncomputable def get_prime_entail_wit_13 : Prop :=
  (
forall (prime_pre : Int) (flag_pre : Int) (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (tot : Int) (i : Int) (PreH1 : (i > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= (n_pre + 1))) (PreH6 : ((0 : Int) <= tot)) (PreH7 : (tot < i)) (PreH8 : (EulerOuterState n_pre i tot flag_l_2 prime_l_2)) ,
  (intArray.seg flag_pre 2 (n_pre + 1) flag_l_2)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime_l_2)
|--
  EX flag_l : (List Int), EX prime_l : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 46340) ” &&
  “ ((0 : Int) <= tot) ” &&
  “ (tot <= n_pre) ” &&
  “ (EulerOuterState n_pre (n_pre + 1) tot flag_l prime_l) ”
  &&  (intArray.seg flag_pre 2 (n_pre + 1) flag_l)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime_l)
) \/
(
forall (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (tot : Int) (i : Int) (PreH1 : (i > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= (n_pre + 1))) (PreH6 : ((0 : Int) <= tot)) (PreH7 : (tot < i)) (PreH8 : (EulerOuterState n_pre i tot flag_l_2 prime_l_2)) ,
  TT && emp 
|--
  “ (EulerOuterState n_pre (n_pre + 1) tot flag_l_2 prime_l_2) ”
  &&  emp
)

noncomputable def get_prime_entail_wit_13_split_goal_1 : Prop :=
  forall (n_pre : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (tot : Int) (i : Int) (PreH1 : (i > n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= (n_pre + 1))) (PreH6 : ((0 : Int) <= tot)) (PreH7 : (tot < i)) (PreH8 : (EulerOuterState n_pre i tot flag_l_2 prime_l_2)) ,
  (EulerOuterState n_pre (n_pre + 1) tot flag_l_2 prime_l_2)

noncomputable def get_prime_return_wit_1 : Prop :=
  forall (prime_pre : Int) (flag_pre : Int) (n_pre : Int) (flag_l : (List Int)) (prime_l : (List Int)) (tot : Int) (flag_l_2 : (List Int)) (prime_l_2 : (List Int)) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : ((0 : Int) <= tot)) (PreH4 : (tot <= n_pre)) (PreH5 : (EulerSieveResult n_pre tot flag_l_2 prime_l_2)) (PreH6 : (2 <= n_pre)) (PreH7 : (n_pre <= 46340)) (PreH8 : ((0 : Int) <= tot)) (PreH9 : (tot <= n_pre)) (PreH10 : (EulerOuterState n_pre (n_pre + 1) tot flag_l prime_l)) ,
  (intArray.seg flag_pre 2 (n_pre + 1) flag_l_2)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime_l_2)
|--
  EX final_tot : Int, EX flag_out : (List Int), EX prime_out : (List Int),
  “ (prime_pre = prime_pre) ” &&
  “ (EulerSieveResult n_pre final_tot flag_out prime_out) ”
  &&  (intArray.seg flag_pre 2 (n_pre + 1) flag_out)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime_out)

noncomputable def get_prime_partial_solve_wit_1 : Prop :=
  forall (prime_pre : Int) (flag_pre : Int) (n_pre : Int) (prime0 : (List Int)) (flag_l : (List Int)) (i : Int) (tot : Int) (PreH1 : (i <= n_pre)) (PreH2 : (tot = (0 : Int))) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : (EulerInitPrefix n_pre i flag_l)) ,
  (intArray.seg flag_pre 2 (n_pre + 1) flag_l)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime0)
|--
  “ (i <= n_pre) ” &&
  “ (tot = (0 : Int)) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 46340) ” &&
  “ (2 <= i) ” &&
  “ (i <= (n_pre + 1)) ” &&
  “ (EulerInitPrefix n_pre i flag_l) ”
  &&  (((flag_pre + (i * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i flag_pre i 2 (n_pre + 1) flag_l)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime0)

noncomputable def get_prime_partial_solve_wit_2 : Prop :=
  forall (prime_pre : Int) (flag_pre : Int) (n_pre : Int) (flag_l : (List Int)) (prime_l : (List Int)) (tot : Int) (i : Int) (PreH1 : (i <= n_pre)) (PreH2 : (2 <= n_pre)) (PreH3 : (n_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i <= (n_pre + 1))) (PreH6 : ((0 : Int) <= tot)) (PreH7 : (tot < i)) (PreH8 : (EulerOuterState n_pre i tot flag_l prime_l)) ,
  (intArray.seg flag_pre 2 (n_pre + 1) flag_l)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime_l)
|--
  “ (i <= n_pre) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 46340) ” &&
  “ (2 <= i) ” &&
  “ (i <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= tot) ” &&
  “ (tot < i) ” &&
  “ (EulerOuterState n_pre i tot flag_l prime_l) ”
  &&  (((flag_pre + (i * sizeof(INT)))) # Int |-> ((Znth (i - 2) flag_l (0 : Int))))
  ** (intArray.missing_i flag_pre i 2 (n_pre + 1) flag_l)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime_l)

noncomputable def get_prime_partial_solve_wit_3 : Prop :=
  forall (prime_pre : Int) (flag_pre : Int) (n_pre : Int) (flag_l : (List Int)) (prime_l : (List Int)) (tot : Int) (i : Int) (PreH1 : ((Znth (i - 2) flag_l (0 : Int)) = i)) (PreH2 : (i <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= (n_pre + 1))) (PreH7 : ((0 : Int) <= tot)) (PreH8 : (tot < i)) (PreH9 : (EulerOuterState n_pre i tot flag_l prime_l)) ,
  (intArray.seg flag_pre 2 (n_pre + 1) flag_l)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime_l)
|--
  “ ((Znth (i - 2) flag_l (0 : Int)) = i) ” &&
  “ (i <= n_pre) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 46340) ” &&
  “ (2 <= i) ” &&
  “ (i <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= tot) ” &&
  “ (tot < i) ” &&
  “ (EulerOuterState n_pre i tot flag_l prime_l) ”
  &&  (((prime_pre + ((tot + 1) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i prime_pre (tot + 1) 1 (n_pre + 1) prime_l)
  ** (intArray.seg flag_pre 2 (n_pre + 1) flag_l)

noncomputable def get_prime_partial_solve_wit_4 : Prop :=
  forall (prime_pre : Int) (flag_pre : Int) (n_pre : Int) (flag_l : (List Int)) (prime_l : (List Int)) (j : Int) (tot : Int) (i : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (2 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (1 <= tot)) (PreH6 : (tot <= n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= tot)) (PreH9 : (EulerInnerState n_pre i j tot flag_l prime_l)) (PreH10 : (2 <= (Znth (j - 1) prime_l (0 : Int)))) (PreH11 : ((Znth (j - 1) prime_l (0 : Int)) <= i)) (PreH12 : ((i * (Znth (j - 1) prime_l (0 : Int))) <= INT_MAX)) ,
  (intArray.seg flag_pre 2 (n_pre + 1) flag_l)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime_l)
|--
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 46340) ” &&
  “ (2 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= tot) ” &&
  “ (tot <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= tot) ” &&
  “ (EulerInnerState n_pre i j tot flag_l prime_l) ” &&
  “ (2 <= (Znth (j - 1) prime_l (0 : Int))) ” &&
  “ ((Znth (j - 1) prime_l (0 : Int)) <= i) ” &&
  “ ((i * (Znth (j - 1) prime_l (0 : Int))) <= INT_MAX) ”
  &&  (((prime_pre + (j * sizeof(INT)))) # Int |-> ((Znth (j - 1) prime_l (0 : Int))))
  ** (intArray.missing_i prime_pre j 1 (n_pre + 1) prime_l)
  ** (intArray.seg flag_pre 2 (n_pre + 1) flag_l)

noncomputable def get_prime_partial_solve_wit_5 : Prop :=
  forall (prime_pre : Int) (flag_pre : Int) (n_pre : Int) (flag_l : (List Int)) (prime_l : (List Int)) (j : Int) (tot : Int) (i : Int) (PreH1 : (j <= tot)) (PreH2 : ((i * (Znth (j - 1) prime_l (0 : Int))) <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (1 <= tot)) (PreH8 : (tot <= n_pre)) (PreH9 : (1 <= j)) (PreH10 : (j <= tot)) (PreH11 : (EulerInnerState n_pre i j tot flag_l prime_l)) (PreH12 : (2 <= (Znth (j - 1) prime_l (0 : Int)))) (PreH13 : ((Znth (j - 1) prime_l (0 : Int)) <= i)) (PreH14 : ((i * (Znth (j - 1) prime_l (0 : Int))) <= INT_MAX)) ,
  (intArray.seg prime_pre 1 (n_pre + 1) prime_l)
  ** (intArray.seg flag_pre 2 (n_pre + 1) flag_l)
|--
  “ (j <= tot) ” &&
  “ ((i * (Znth (j - 1) prime_l (0 : Int))) <= n_pre) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 46340) ” &&
  “ (2 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= tot) ” &&
  “ (tot <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= tot) ” &&
  “ (EulerInnerState n_pre i j tot flag_l prime_l) ” &&
  “ (2 <= (Znth (j - 1) prime_l (0 : Int))) ” &&
  “ ((Znth (j - 1) prime_l (0 : Int)) <= i) ” &&
  “ ((i * (Znth (j - 1) prime_l (0 : Int))) <= INT_MAX) ”
  &&  (((prime_pre + (j * sizeof(INT)))) # Int |-> ((Znth (j - 1) prime_l (0 : Int))))
  ** (intArray.missing_i prime_pre j 1 (n_pre + 1) prime_l)
  ** (intArray.seg flag_pre 2 (n_pre + 1) flag_l)

noncomputable def get_prime_partial_solve_wit_6 : Prop :=
  forall (prime_pre : Int) (flag_pre : Int) (n_pre : Int) (flag_l : (List Int)) (prime_l : (List Int)) (j : Int) (tot : Int) (i : Int) (PreH1 : (j <= tot)) (PreH2 : ((i * (Znth (j - 1) prime_l (0 : Int))) <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (1 <= tot)) (PreH8 : (tot <= n_pre)) (PreH9 : (1 <= j)) (PreH10 : (j <= tot)) (PreH11 : (EulerInnerState n_pre i j tot flag_l prime_l)) (PreH12 : (2 <= (Znth (j - 1) prime_l (0 : Int)))) (PreH13 : ((Znth (j - 1) prime_l (0 : Int)) <= i)) (PreH14 : ((i * (Znth (j - 1) prime_l (0 : Int))) <= INT_MAX)) ,
  (intArray.seg prime_pre 1 (n_pre + 1) prime_l)
  ** (intArray.seg flag_pre 2 (n_pre + 1) flag_l)
|--
  “ (j <= tot) ” &&
  “ ((i * (Znth (j - 1) prime_l (0 : Int))) <= n_pre) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 46340) ” &&
  “ (2 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= tot) ” &&
  “ (tot <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= tot) ” &&
  “ (EulerInnerState n_pre i j tot flag_l prime_l) ” &&
  “ (2 <= (Znth (j - 1) prime_l (0 : Int))) ” &&
  “ ((Znth (j - 1) prime_l (0 : Int)) <= i) ” &&
  “ ((i * (Znth (j - 1) prime_l (0 : Int))) <= INT_MAX) ”
  &&  (((prime_pre + (j * sizeof(INT)))) # Int |-> ((Znth (j - 1) prime_l (0 : Int))))
  ** (intArray.missing_i prime_pre j 1 (n_pre + 1) prime_l)
  ** (intArray.seg flag_pre 2 (n_pre + 1) flag_l)

noncomputable def get_prime_partial_solve_wit_7 : Prop :=
  forall (prime_pre : Int) (flag_pre : Int) (n_pre : Int) (flag_l : (List Int)) (prime_l : (List Int)) (j : Int) (tot : Int) (i : Int) (PreH1 : (j <= tot)) (PreH2 : ((i * (Znth (j - 1) prime_l (0 : Int))) <= n_pre)) (PreH3 : (2 <= n_pre)) (PreH4 : (n_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (1 <= tot)) (PreH8 : (tot <= n_pre)) (PreH9 : (1 <= j)) (PreH10 : (j <= tot)) (PreH11 : (EulerInnerState n_pre i j tot flag_l prime_l)) (PreH12 : (2 <= (Znth (j - 1) prime_l (0 : Int)))) (PreH13 : ((Znth (j - 1) prime_l (0 : Int)) <= i)) (PreH14 : ((i * (Znth (j - 1) prime_l (0 : Int))) <= INT_MAX)) ,
  (intArray.seg prime_pre 1 (n_pre + 1) prime_l)
  ** (intArray.seg flag_pre 2 (n_pre + 1) flag_l)
|--
  “ (j <= tot) ” &&
  “ ((i * (Znth (j - 1) prime_l (0 : Int))) <= n_pre) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 46340) ” &&
  “ (2 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= tot) ” &&
  “ (tot <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= tot) ” &&
  “ (EulerInnerState n_pre i j tot flag_l prime_l) ” &&
  “ (2 <= (Znth (j - 1) prime_l (0 : Int))) ” &&
  “ ((Znth (j - 1) prime_l (0 : Int)) <= i) ” &&
  “ ((i * (Znth (j - 1) prime_l (0 : Int))) <= INT_MAX) ”
  &&  (((flag_pre + ((i * (Znth (j - 1) prime_l (0 : Int))) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i flag_pre (i * (Znth (j - 1) prime_l (0 : Int))) 2 (n_pre + 1) flag_l)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime_l)

noncomputable def get_prime_partial_solve_wit_8 : Prop :=
  forall (prime_pre : Int) (flag_pre : Int) (n_pre : Int) (flag_l : (List Int)) (prime_l : (List Int)) (i : Int) (tot : Int) (j : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : (2 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (1 <= tot)) (PreH6 : (tot <= n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= tot)) (PreH9 : ((i * (Znth (j - 1) prime_l (0 : Int))) <= n_pre)) (PreH10 : (EulerInnerMarkedState n_pre i j tot flag_l prime_l)) (PreH11 : (2 <= (Znth (j - 1) prime_l (0 : Int)))) (PreH12 : ((Znth (j - 1) prime_l (0 : Int)) <= i)) ,
  (intArray.seg flag_pre 2 (n_pre + 1) flag_l)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime_l)
|--
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 46340) ” &&
  “ (2 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= tot) ” &&
  “ (tot <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= tot) ” &&
  “ ((i * (Znth (j - 1) prime_l (0 : Int))) <= n_pre) ” &&
  “ (EulerInnerMarkedState n_pre i j tot flag_l prime_l) ” &&
  “ (2 <= (Znth (j - 1) prime_l (0 : Int))) ” &&
  “ ((Znth (j - 1) prime_l (0 : Int)) <= i) ”
  &&  (((prime_pre + (j * sizeof(INT)))) # Int |-> ((Znth (j - 1) prime_l (0 : Int))))
  ** (intArray.missing_i prime_pre j 1 (n_pre + 1) prime_l)
  ** (intArray.seg flag_pre 2 (n_pre + 1) flag_l)

noncomputable def get_prime_partial_solve_wit_9_pure : Prop :=
  forall (prime_pre : Int) (flag_pre : Int) (n_pre : Int) (flag_l : (List Int)) (prime_l : (List Int)) (tot : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : ((0 : Int) <= tot)) (PreH4 : (tot <= n_pre)) (PreH5 : (EulerOuterState n_pre (n_pre + 1) tot flag_l prime_l)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "flag" ) )) # Ptr |-> (flag_pre))
  ** ((( &( "prime" ) )) # Ptr |-> (prime_pre))
  ** ((( &( "tot" ) )) # Int |-> (tot))
  ** (intArray.seg flag_pre 2 (n_pre + 1) flag_l)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime_l)
|--
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 46340) ” &&
  “ ((0 : Int) <= tot) ” &&
  “ (tot <= n_pre) ” &&
  “ (EulerOuterState n_pre (n_pre + 1) tot flag_l prime_l) ”

noncomputable def get_prime_partial_solve_wit_9_aux : Prop :=
  forall (prime_pre : Int) (flag_pre : Int) (n_pre : Int) (flag_l : (List Int)) (prime_l : (List Int)) (tot : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : ((0 : Int) <= tot)) (PreH4 : (tot <= n_pre)) (PreH5 : (EulerOuterState n_pre (n_pre + 1) tot flag_l prime_l)) ,
  (intArray.seg flag_pre 2 (n_pre + 1) flag_l)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime_l)
|--
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 46340) ” &&
  “ ((0 : Int) <= tot) ” &&
  “ (tot <= n_pre) ” &&
  “ (EulerOuterState n_pre (n_pre + 1) tot flag_l prime_l) ” &&
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 46340) ” &&
  “ ((0 : Int) <= tot) ” &&
  “ (tot <= n_pre) ” &&
  “ (EulerOuterState n_pre (n_pre + 1) tot flag_l prime_l) ”
  &&  (intArray.seg flag_pre 2 (n_pre + 1) flag_l)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime_l)

noncomputable def get_prime_partial_solve_wit_9 : Prop := get_prime_partial_solve_wit_9_pure -> get_prime_partial_solve_wit_9_aux

noncomputable def get_prime_which_implies_wit_1 : Prop :=
  (
forall (prime_pre : Int) (flag_pre : Int) (n_pre : Int) (prime_l_2 : (List Int)) (flag_l_2 : (List Int)) (tot : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : ((0 : Int) <= tot)) (PreH4 : (tot <= n_pre)) (PreH5 : (EulerOuterState n_pre (n_pre + 1) tot flag_l_2 prime_l_2)) ,
  (intArray.seg flag_pre 2 (n_pre + 1) flag_l_2)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime_l_2)
|--
  EX flag_l : (List Int), EX prime_l : (List Int),
  “ (2 <= n_pre) ” &&
  “ (n_pre <= 46340) ” &&
  “ ((0 : Int) <= tot) ” &&
  “ (tot <= n_pre) ” &&
  “ (EulerSieveResult n_pre tot flag_l prime_l) ”
  &&  (intArray.seg flag_pre 2 (n_pre + 1) flag_l)
  ** (intArray.seg prime_pre 1 (n_pre + 1) prime_l)
) \/
(
forall (n_pre : Int) (prime_l_2 : (List Int)) (flag_l_2 : (List Int)) (tot : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : ((0 : Int) <= tot)) (PreH4 : (tot <= n_pre)) (PreH5 : (EulerOuterState n_pre (n_pre + 1) tot flag_l_2 prime_l_2)) ,
  TT && emp 
|--
  “ (EulerSieveResult n_pre tot flag_l_2 prime_l_2) ”
  &&  emp
)

noncomputable def get_prime_which_implies_wit_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (prime_l_2 : (List Int)) (flag_l_2 : (List Int)) (tot : Int) (PreH1 : (2 <= n_pre)) (PreH2 : (n_pre <= 46340)) (PreH3 : ((0 : Int) <= tot)) (PreH4 : (tot <= n_pre)) (PreH5 : (EulerOuterState n_pre (n_pre + 1) tot flag_l_2 prime_l_2)) ,
  (EulerSieveResult n_pre tot flag_l_2 prime_l_2)


structure VC_Correct : Type where
  proof_of_get_prime_safety_wit_1 : get_prime_safety_wit_1
  proof_of_get_prime_safety_wit_2 : get_prime_safety_wit_2
  proof_of_get_prime_safety_wit_3 : get_prime_safety_wit_3
  proof_of_get_prime_safety_wit_4 : get_prime_safety_wit_4
  proof_of_get_prime_safety_wit_5 : get_prime_safety_wit_5
  proof_of_get_prime_safety_wit_6 : get_prime_safety_wit_6
  proof_of_get_prime_safety_wit_7 : get_prime_safety_wit_7
  proof_of_get_prime_safety_wit_8 : get_prime_safety_wit_8
  proof_of_get_prime_safety_wit_9 : get_prime_safety_wit_9
  proof_of_get_prime_safety_wit_10 : get_prime_safety_wit_10
  proof_of_get_prime_safety_wit_11 : get_prime_safety_wit_11
  proof_of_get_prime_safety_wit_12 : get_prime_safety_wit_12
  proof_of_get_prime_safety_wit_13 : get_prime_safety_wit_13
  proof_of_get_prime_safety_wit_14 : get_prime_safety_wit_14
  proof_of_get_prime_entail_wit_4 : get_prime_entail_wit_4
  proof_of_get_prime_entail_wit_6 : get_prime_entail_wit_6
  proof_of_get_prime_entail_wit_12 : get_prime_entail_wit_12
  proof_of_get_prime_return_wit_1 : get_prime_return_wit_1
  proof_of_get_prime_partial_solve_wit_1 : get_prime_partial_solve_wit_1
  proof_of_get_prime_partial_solve_wit_2 : get_prime_partial_solve_wit_2
  proof_of_get_prime_partial_solve_wit_3 : get_prime_partial_solve_wit_3
  proof_of_get_prime_partial_solve_wit_4 : get_prime_partial_solve_wit_4
  proof_of_get_prime_partial_solve_wit_5 : get_prime_partial_solve_wit_5
  proof_of_get_prime_partial_solve_wit_6 : get_prime_partial_solve_wit_6
  proof_of_get_prime_partial_solve_wit_7 : get_prime_partial_solve_wit_7
  proof_of_get_prime_partial_solve_wit_8 : get_prime_partial_solve_wit_8
  proof_of_get_prime_partial_solve_wit_9_pure : get_prime_partial_solve_wit_9_pure
  proof_of_get_prime_partial_solve_wit_9 : get_prime_partial_solve_wit_9
  proof_of_get_prime_entail_wit_1 : get_prime_entail_wit_1
  proof_of_get_prime_entail_wit_2 : get_prime_entail_wit_2
  proof_of_get_prime_entail_wit_3 : get_prime_entail_wit_3
  proof_of_get_prime_entail_wit_5_1 : get_prime_entail_wit_5_1
  proof_of_get_prime_entail_wit_5_2 : get_prime_entail_wit_5_2
  proof_of_get_prime_entail_wit_7 : get_prime_entail_wit_7
  proof_of_get_prime_entail_wit_8 : get_prime_entail_wit_8
  proof_of_get_prime_entail_wit_9 : get_prime_entail_wit_9
  proof_of_get_prime_entail_wit_10 : get_prime_entail_wit_10
  proof_of_get_prime_entail_wit_11_1 : get_prime_entail_wit_11_1
  proof_of_get_prime_entail_wit_11_2 : get_prime_entail_wit_11_2
  proof_of_get_prime_entail_wit_13 : get_prime_entail_wit_13
  proof_of_get_prime_which_implies_wit_1 : get_prime_which_implies_wit_1

end Algorithms.sieve_of_euler.lean.groundtruth.sieve_of_euler_goal
