module

import Formalism.SharpRestriction.LevelLetterCocycles.TwGood
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Mathlib.RingTheory.DedekindDomain.Factorization

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions
open scoped NNReal

namespace Formalism.L2.TwC

section rings

variable (l : ℕ) [Fact l.Prime]

def intOf (K : IntermediateField ℚ_[l] (PadicAlgCl l)) : Subring (PadicAlgCl l) :=
  K.toSubalgebra.toSubring ⊓ (PadicAlgCl.valued l).v.integer

def clC (F : IntermediateField ℚ_[l] (PadicAlgCl l)) : Subring ℂ_[l] :=
  (F.toSubalgebra.toSubring.map (algebraMap (PadicAlgCl l) ℂ_[l])).topologicalClosure ⊓
    (PadicComplexInt l).toSubring

def Kt (K₀ L : Loc.FinExt l) : IntermediateField ℚ_[l] (PadicAlgCl l) :=
  K₀.1 ⊔ L.1 ⊔ Loc.MaximalUnramifiedExtension l

def muK (k : ℕ) : IntermediateField ℚ_[l] (PadicAlgCl l) :=
  IntermediateField.adjoin ℚ_[l] {x | x ^ (l ^ k) = 1}

end rings

section places

theorem placesOver_finite' (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p ≠ 0) :
    (placesOver E p).Finite := by
  apply _root_.Formalism.MainNotions.placesOver_finite_av <;> assumption

def pDC {R : Ranks} (H : Host R) (l : ℕ) : Finset (HeightOneSpectrum (𝓞 H.E)) :=
  (placesOver_finite' H.E (if l = H.pde then H.pde' else H.pde)
    (by split_ifs <;> first | exact H.pde'_prime.ne_zero | exact H.pde_prime.ne_zero)).toFinset

theorem coe_pDC {R : Ranks} (H : Host R) (l : ℕ) :
    (pDC H l : Set (HeightOneSpectrum (𝓞 H.E))) = placesOver H.E (if l = H.pde then H.pde' else H.pde) := by
  first
    | exact Set.Finite.coe_toFinset _

end places

end Formalism.L2.TwC
