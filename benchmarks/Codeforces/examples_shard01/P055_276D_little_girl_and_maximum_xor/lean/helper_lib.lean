import Codeforces.examples_shard01.P055_276D_little_girl_and_maximum_xor.lean.spec_lib

namespace Codeforces.examples_shard01.P055_276D_little_girl_and_maximum_xor.lean

open AUXLib

open MaxMinLib

def HighestBitScan (l r x b : Int) : Prop :=
  x = Z.lxor l r ∧ ∀ k, (b < k ∧ k ≤ 63) → Z.land (Z.shiftr x k) 1 = 0

end Codeforces.examples_shard01.P055_276D_little_girl_and_maximum_xor.lean
