module

public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle065
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle063
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle115
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PhiTTransport
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedInvMulLe
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle463
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle299
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle064
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaAtEqSumHeisOfFourierSum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacewiseToAdelicDecompositionForall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergOperatorFinitePartLatticeVacuumSign
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHomLatticeIffIntegralMatrixSplitChart
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle006
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsDiscriminantTwelfthRootOfIdealLatticeIffDelta1
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.PlaceModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocReduction

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T S0 T0 : HSp D} {m n : ℕ}

theorem isHalf_smul {e : AE D} {u : Mx D m n} : IsHalf e u ↔ e • u = u :=
  ⟨fun h => Matrix.ext h, fun h i j => congrFun (congrFun h i) j⟩

theorem heis_add {x y : WO S T} (h : symplO S T x y = 0) (f : WO S T → ℂ) :
    heisO ψ S T (x + y) f = heisO ψ S T x (heisO ψ S T y f) := by
  have := heisL_heisL S T ψ x y f
  rw [symplOH, h, mul_zero, AddChar.map_zero_eq_one, one_smul] at this
  exact this.symm

theorem heis_comm (x y : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T x (heisO ψ S T y f) = ψ (symplO S T x y) • heisO ψ S T y (heisO ψ S T x f) := heisL_comm S T ψ x y f

theorem heis_smul (x : WO S T) (c : ℂ) (f : WO S T → ℂ) : heisO ψ S T x (c • f) = c • heisO ψ S T x f :=
  (heisL S T ψ x).map_smul c f

section Model

variable {e : AE D} {Λ : AddSubgroup (WO S T)} {f₀ : WO S T → ℂ} {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}

theorem fix_half (h₁ : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Tm) {u : WO S T} (hu : u ∈ Λ)
    (hu' : IsHalf e u) : heisO ψ S T u f₀ = f₀ := by
  have v1 := h₁.vac
  rw [one_smul] at v1
  rw [← v1, ← h₁.trans _ (GlobalTheory.isSBHalf_halfInd e Λ) u hu']
  congr 1
  funext t
  rw [halfInd_eq_ind]
  exact ind_add _ t (AddSubgroup.mem_inf.2 ⟨hu, (isHalf_iff S T).1 hu'⟩)

theorem fix_conj (hLL' : ∀ u ∈ Λ, IsHalf e u → ∀ y ∈ Λ, IsHalf (cA D e) y → ψ (symplO S T u y) = 1)
    (h₁ : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Tm) {u : WO S T} (hu : u ∈ Λ)
    (hu' : IsHalf (cA D e) u) : heisO ψ S T u f₀ = f₀ := by
  have v1 := h₁.vac
  rw [one_smul] at v1
  rw [← v1, ← h₁.modul _ (GlobalTheory.isSBHalf_halfInd e Λ) u hu']
  congr 1
  funext t
  unfold halfInd
  split_ifs with h
  · rw [hLL' t h.1 h.2 u hu hu', mul_one]
  · rw [mul_zero]

end Model

section Periodic

open GlobalTheory.MixModel

variable {μ : Measure (Mx D m n)} {𝓕 : Set (Mx D m n)}

end Periodic

section Red

variable {jA jB : Mx D m n →+ WO S T} {j0 : WO S0 T0 →+ WO S T} {μ : Measure (Mx D m n)} {𝓕 : Set (Mx D m n)}
  (hAA : ∀ a a', symplO S T (jA a) (jA a') = 0) (hA0 : ∀ a z, symplO S T (jA a) (j0 z) = 0)
  (h00 : ∀ z z', symplO S T (j0 z) (j0 z') = symplO S0 T0 z z')
  (hrat : ∀ γ ∈ GlobalTheory.MixModel.ratMx D m n, ∃ x, jA γ = ratW T S x) (hcont : Continuous jA)
  (hμ : μ.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain (GlobalTheory.MixModel.ratMx D m n) 𝓕 μ)

end Red

section Main

variable {jA jB : Mx D m n →+ WO S T} {j0 : WO S0 T0 →+ WO S T} {e : AE D} {Λ : AddSubgroup (WO S T)}
  {Λ0 : AddSubgroup (WO S0 T0)}
  (sA : ∀ (c : AE D) a, jA (c • a) = c • jA a) (sB : ∀ (c : AE D) b, jB (c • b) = c • jB b)
  (s0 : ∀ (c : AE D) z, j0 (c • z) = c • j0 z)
  (hAA : ∀ a a', symplO S T (jA a) (jA a') = 0) (hBB : ∀ b b', symplO S T (jB b) (jB b') = 0)
  (hA0 : ∀ a z, symplO S T (jA a) (j0 z) = 0) (hB0 : ∀ b z, symplO S T (jB b) (j0 z) = 0)
  (h00 : ∀ z z', symplO S T (j0 z) (j0 z') = symplO S0 T0 z z')
  (hdec : ∀ x : WO S T, ∃ a b z, x = jA a + jB b + j0 z)
  (hhalf : ∀ (c : AE D) a b z, IsHalf c (jA a + jB b + j0 z) → IsHalf c a ∧ IsHalf c b ∧ IsHalf c z)
  (hLL' : ∀ u ∈ Λ, IsHalf e u → ∀ y ∈ Λ, IsHalf (cA D e) y → ψ (symplO S T u y) = 1)
  (hX : ∀ x, IsHalf e x → (∀ y ∈ Λ, IsHalf (cA D e) y → ψ (symplO S T x y) = 1) → x ∈ Λ)
  (hY : ∀ y, IsHalf (cA D e) y → (∀ x ∈ Λ, IsHalf e x → ψ (symplO S T x y) = 1) → y ∈ Λ)
  (hsp : ∀ a b z, IsHalf e a → IsHalf e b → IsHalf e z →
    (jA a + jB b + j0 z ∈ Λ ↔ jA a ∈ Λ ∧ jB b ∈ Λ ∧ j0 z ∈ Λ))
  (hsp0 : ∀ z, IsHalf e z → (j0 z ∈ Λ ↔ z ∈ Λ0))

variable {μw : Measure (Mx D m n)} (hψ : IsStdChar D ψ (-1)) (hcont : Continuous jA)
  (hcl : IsClosed {x : WO S T | x ∈ Λ ∧ IsHalf e x})
  (hw0 : μw {a | ¬ IsHalf e a} = 0) (hw1 : ∀ a₀ : Mx D m n, IsHalf e a₀ → Measure.map (fun a => a + a₀) μw = μw)
  (hw2 : μw {a | IsHalf e a ∧ jA a ∈ Λ} = 1)

variable {μ : Measure (Mx D m n)} {𝓕 : Set (Mx D m n)}
  (hrat : ∀ γ ∈ GlobalTheory.MixModel.ratMx D m n, ∃ x, jA γ = ratW T S x)
  (hμ : μ.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain (GlobalTheory.MixModel.ratMx D m n) 𝓕 μ)
  (hec : e * cA D e = 0) (hinf : infPart D e = 0)
  {f₀ : WO S T → ℂ} {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)} (hf₀ : IsThetaFunO ψ S T f₀)
  (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Tm)

end Main

section Lattice

variable {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
  {e : AE D}


open GlobalTheory.PlaceDatum in
theorem lattice_facts (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (he : e * e = e)
    (hinf : infPart D e = 0) :
    (∀ u ∈ latO S T ΛS ΛT fun _ => True, IsHalf e u → ∀ y ∈ latO S T ΛS ΛT fun _ => True, IsHalf (cA D e) y →
      ψ (symplO S T u y) = 1) ∧
    (∀ x, IsHalf e x → (∀ y ∈ latO S T ΛS ΛT fun _ => True, IsHalf (cA D e) y → ψ (symplO S T x y) = 1) →
      x ∈ latO S T ΛS ΛT fun _ => True) ∧
    (∀ y, IsHalf (cA D e) y → (∀ x ∈ latO S T ΛS ΛT fun _ => True, IsHalf e x → ψ (symplO S T x y) = 1) →
      y ∈ latO S T ΛS ΛT fun _ => True) ∧
    (∀ k : ℕ, 0 < k → ∃ R : Set (WO S T), R.Finite ∧ ∀ t ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e,
      ∃ r ∈ R, ∃ u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e, t = r + k • u) ∧
    ∀ y, IsHalf (cA D e) y → ∃ k : ℕ, 0 < k ∧ k • y ∈ latO S T ΛS ΛT fun _ => True := by
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ hS hT).1
  have hfin := GlobalTheory.LatFinMod.latO_finite_mod D S T _ _ hS.1.fg hT.1.fg fun _ => True
  have he' : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, he]
  have hsm : ∀ a : AE D, a * a = a → ∀ u ∈ latO S T ΛS ΛT fun _ => True,
      a • u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T a := fun a ha u hu =>
    AddSubgroup.mem_inf.2 ⟨GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ha])) u hu, by rw [mem_half, smul_smul, ha]⟩
  refine ⟨fun u hu hu' y hy _ => (hdual u (infPart_of_half hinf hu')).1 hu y hy, fun x hx h => ?_, fun y hy h => ?_,
    fun k hk => ?_, fun y hy => exists_nsmul_mem_latO'
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hS)
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hT) y (infPart_of_half (infPart_cA hinf) hy)⟩
  · refine (hdual x (infPart_of_half hinf hx)).2 fun u hu => ?_
    have := h _ (hsm _ he' u hu).1 ((isHalf_iff S T).2 (hsm _ he' u hu).2)
    rwa [← symplO_smul, isHalf_smul.1 hx] at this
  · refine (hdual y (infPart_of_half (infPart_cA hinf) hy)).2 fun u hu => ?_
    have := h _ (hsm _ he u hu).1 ((isHalf_iff S T).2 (hsm _ he u hu).2)
    rw [symplO_smul, isHalf_smul.1 hy] at this
    rw [symplO_skew, ← one_mul (ψ _), ← this, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one, this]
  · obtain ⟨R, hR, h⟩ := hfin k hk
    refine ⟨(fun r => e • r) '' R, hR.image _, fun t ht => ?_⟩
    obtain ⟨r, hr, u, hu, htr⟩ := h t ht.1
    refine ⟨_, ⟨r, hr, rfl⟩, e • u, hsm e he u hu, ?_⟩
    have := (mem_half S T).1 ht.2
    rw [← this, htr, smul_add, smul_comm e k u]

end Lattice

end GlobalTheory.LocReduction

end
end

section

noncomputable section

namespace GlobalTheory.Transport.TwistRead

section Gen

open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 Matrix
open GlobalTheory.Transport.LevelDatum

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] {hc : Formalism.BasicNotions.CMData F E}
  {a b : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

omit [NumberField E] [StarRing E] in
theorem toMatrix_inFr (f : Sp E a ≃ₗ[E] Sp E a) (f' : Sp E b ≃ₗ[E] Sp E b) (x : HomE E a b) :
    LinearMap.toMatrix' f'.toLinearMap * LinearMap.toMatrix' (inFr f f' x) = LinearMap.toMatrix' x * LinearMap.toMatrix' f.toLinearMap := by
  rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_comp]
  exact congrArg _ (LinearMap.ext fun z => f'.apply_symm_apply _)

theorem map_ptFr {n : ℕ} {g : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} (h : IsPtOf hc g p) {P : HeightOneSpectrum (𝓞 E)}
    (hPQ : P ∈ Q) (hPG : P ∉ SG) :
    (LinearMap.toMatrix' (ptFr p P).toLinearMap).map (algebraMap E (P.adicCompletion E)) =
      (g : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F P) := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.map_apply, Matrix.map_apply, LinearMap.toMatrix'_apply, ptFr_of_mem p hPG hPQ]
  exact (h.fr ⟨P, hPQ⟩ i j).symm

omit [StarRing E] in
theorem map_inv_mul_map {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (g : GL (Fin n) (AfE F E)) :
    ((g⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F P) *
      (g : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F P) = 1 := by
  rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem map_read {g : GL (Fin a) (AfE F E)} {g' : GL (Fin b) (AfE F E)} {p : DecoF E a ST SG Q} {p' : DecoF E b ST SG Q}
    (h : IsPtOf hc g p) (h' : IsPtOf hc g' p') {P : HeightOneSpectrum (𝓞 E)} (hPQ : P ∈ Q) (hPG : P ∉ SG) (x : HomE E a b) :
    (LinearMap.toMatrix' (inFr (ptFr p P) (ptFr p' P) x)).map (algebraMap E (P.adicCompletion E)) =
      (mid g g' x).map (adAt F P) := by
  have f1 := congrArg (fun A => Matrix.map A (algebraMap E (P.adicCompletion E))) (toMatrix_inFr (ptFr p P) (ptFr p' P) x)
  simp only [Matrix.map_mul] at f1
  rw [map_ptFr h hPQ hPG, map_ptFr h' hPQ hPG] at f1
  have hx : (LinearMap.toMatrix' x).map (algebraMap E (P.adicCompletion E)) = (adMat F x).map (adAt F P) :=
    Matrix.ext fun i j => (adAt_inclE F P _).symm
  unfold mid
  rw [Matrix.map_mul, Matrix.map_mul, ← hx, Matrix.mul_assoc, ← f1, ← Matrix.mul_assoc, map_inv_mul_map, Matrix.one_mul]

theorem read_sub_le {k y : GL (Fin a) (AfE F E)} {k' y' : GL (Fin b) (AfE F E)} {p q : DecoF E a ST SG Q} {p' q' : DecoF E b ST SG Q}
    (hp : IsPtOf hc k p) (hpN : p.deco.1.N = stdLat E a) (hp' : IsPtOf hc k' p') (hpN' : p'.deco.1.N = stdLat E b)
    (hq : IsPtOf hc (y * k) q) (hq' : IsPtOf hc (y' * k') q') {P : HeightOneSpectrum (𝓞 E)} (hPQ : P ∈ Q) (hPG : P ∉ SG)
    (M₀ : ℕ) (x x₀ : HomE E a b)
    (h : ∀ r s, Valued.v (adAt F P ((mid y y' x - adMat F x₀) r s)) ≤ Valued.v ((M₀ : ℕ) : P.adicCompletion E)) (r : Fin b) (s : Fin a) :
    P.valuation E ((LinearMap.toMatrix' (inFr (ptFr q P) (ptFr q' P) x) - LinearMap.toMatrix' (inFr (ptFr p P) (ptFr p' P) x₀)) r s) ≤
      P.valuation E ((M₀ : ℕ) : E) := by
  have hd : mid (y * k) (y' * k') x - mid k k' x₀ =
      ((k'⁻¹ : GL (Fin b) (AfE F E)) : Matrix (Fin b) (Fin b) (AfE F E)) * (mid y y' x - adMat F x₀) *
        (k : Matrix (Fin a) (Fin a) (AfE F E)) := by
    unfold mid
    rw [_root_.mul_inv_rev, Units.val_mul, Units.val_mul, Matrix.mul_sub, Matrix.sub_mul]
    simp only [Matrix.mul_assoc]
  have hA : ∀ r s, Valued.v (adAt F P (((k'⁻¹ : GL (Fin b) (AfE F E)) : Matrix (Fin b) (Fin b) (AfE F E)) r s)) ≤ 1 := fun r s => by
    have := Splice.valued_inv_mul_le (w := P) (hpN' ▸ hp'.lat) (carries_one (F := F) b) le_rfl r s
    rwa [mul_one] at this
  have hK : ∀ r s, Valued.v (adAt F P ((k : Matrix (Fin a) (Fin a) (AfE F E)) r s)) ≤ 1 := fun r s => by
    have := Splice.valued_inv_mul_le (w := P) (carries_one (F := F) a) (hpN ▸ hp.lat) le_rfl r s
    rwa [inv_one, one_mul] at this
  have e1 := congrFun (congrFun (map_read hq hq' hPQ hPG x) r) s
  have e2 := congrFun (congrFun (map_read hp hp' hPQ hPG x₀) r) s
  simp only [Matrix.map_apply] at e1 e2
  rw [← valued_algebraMap, ← valued_algebraMap, map_natCast, Matrix.sub_apply, map_sub, e1, e2, ← map_sub, ← Matrix.sub_apply, hd]

  rw [Matrix.mul_apply, map_sum]
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [map_mul, map_mul]
  refine (mul_le_of_le_one_right' (hK j s)).trans ?_

  rw [Matrix.mul_apply, map_sum]
  refine Valuation.map_sum_le _ fun l _ => ?_
  rw [map_mul, map_mul]
  exact (mul_le_of_le_one_left' (hA r l)).trans (h l j)

end Gen

end GlobalTheory.Transport.TwistRead

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.Ker

namespace GlobalTheory.Transport.TwistRead

theorem qread : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (u : B.Word) (a : I.ι) (i : ℕ) (P : Formalism.L2.Col.rowSG (B.primes X) I.sel (I.tup a)),
    P.1 ∈ I.Q a → Disjoint (B.primes X).vGs (I.Q a) →
    ∀ (p q : PtAt B.R I.sel (I.tup a) (I.cst a) u i) (p' q' : PtAt B.R I.sel (I.tup a) (I.cst a) u (i + 1))
    (k y : TC.GA B (B.R.N i)) (k' y' : TC.GA B (B.R.N (i + 1))),
    TC.PtOf k p.1.1 → p.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N i) →
    TC.PtOf k' p'.1.1 → p'.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N (i + 1)) →
    TC.PtOf (y * k) q.1.1 → TC.PtOf (y' * k') q'.1.1 →
    ∀ (M₀ : ℕ) (x x₀ : Formalism.L2.Col.HomE B.fields.E (B.R.N i) (B.R.N (i + 1))),
      GlobalTheory.Transport.CongAt B P.1 M₀ y y' x x₀ →
      ∀ r s, P.1.valuation B.fields.E
        ((LinearMap.toMatrix' (Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) q.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) q'.1.1 P) x) -
          LinearMap.toMatrix' (Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) p.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) p'.1.1 P) x₀)) r s) ≤
        P.1.valuation B.fields.E ((M₀ : ℕ) : B.fields.E) := by
  intro B X I u a i P hP hd p q p' q' k y k' y' hp hpN hp' hpN' hq hq' M₀ x x₀ hC r s
  rw [frsF_eq_ptFr, frsF_eq_ptFr, frsF_eq_ptFr, frsF_eq_ptFr]
  exact read_sub_le hp hpN hp' hpN' hq hq' hP (Finset.disjoint_right.1 hd hP) M₀ x x₀ (fun r s => hC r s) r s

end GlobalTheory.Transport.TwistRead
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
open GlobalTheory.Mem.Col2.AdT
open Filter Topology


theorem _root_.GlobalTheory.T.exists_badPrime_over_chart_bad_place : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), v ∈ Formalism.L2.Forms.badG (I.rec7 l Z) ∨ I.UnderQ a v → ∃ P : SBof I a, Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) := by
  exact @GlobalTheory.Mem.Col2.AdT.exists_SBof_over_sub
end

section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.archimedean_parameters_addChar_unique : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ l l' : D.what₂.Tau → ℝ, HasRealPar ψ θ l → HasRealPar ψ θ l' → l = l' := by
  first | exact @GlobalTheory.StdUnn.RealPar.realPar_unique | exact GlobalTheory.StdUnn.RealPar.realPar_unique | (intros; apply GlobalTheory.StdUnn.RealPar.realPar_unique <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IdemSumLoc

variable {D : D7}

theorem idem_mul_sum {es : Formalism.L2.DIV.Pl D.host.E → AE D} {S : Finset (Formalism.L2.DIV.Pl D.host.E)}
    (hes : ∀ Q ∈ S, Formalism.L2.NTheta.IsIdemAt (es Q) Q) (hc : (∑ Q ∈ S, es Q) * cA D (∑ Q ∈ S, es Q) = 0)
    {P : Formalism.L2.DIV.Pl D.host.E} (hP : P ∈ S) : es P * ∑ Q ∈ S, es Q = es P := by
  have h1 : ∀ i ∈ S, es i * es i = es i := fun i hi => (hes i hi).1.1
  have hcross : ∀ i ∈ S, ∀ j ∈ S, es i * cA D (es j) = 0 :=
    GlobalTheory.PlaceDatum.cross_eq_zero (R := AE D) GlobalTheory.PlaceDatum.isUnit_natCast (cA D) es S h1 hc
  rw [Finset.mul_sum, Finset.sum_eq_single P
    (fun Q hQ hQP => GlobalTheory.PlaceDatum.idemAt_mul (hes P hP) (hes Q hQ) (hcross P hP Q hQ) (hcross Q hQ P hP) hQP)
    (fun h => absurd hP h), h1 P hP]

end GlobalTheory.IdemSumLoc

namespace GlobalTheory.IdemSumLoc

end GlobalTheory.IdemSumLoc
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IdemSumVac

variable {D : D7}

theorem symplOH_eq_zero_of_hO {S T : HSp D} {u u' : WO S T} (h : hO S T u u' = 0) : symplOH S T u u' = 0 := by
  rw [symplOH, symplO, h, mul_zero, map_zero, mul_zero]

theorem heisO_sum_smul (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Λ : AddSubgroup (WO S T)) (f : WO S T → ℂ)
    (hf : IsLatVac (heisO ψ S T) Λ f) (hΛ : ∀ w : AE D, finPart D w ∈ intAE D → ∀ u ∈ Λ, w • u ∈ Λ)
    {ι : Type} (p : ι → AE D) (s : Finset ι) (hs : ∀ i ∈ s, IsSplitIdem D (p i))
    (hc : ∀ i ∈ s, ∀ j ∈ s, p i * cA D (p j) = 0) (x : WO S T) (hx : x ∈ Λ) :
    heisO ψ S T ((∑ i ∈ s, p i) • x) f = f := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, zero_smul]; exact GlobalTheory.LatVac.heisO_zero ψ f
  | insert a s ha ih =>
    have hsa := hs a (Finset.mem_insert_self _ _)
    have ih' := ih (fun i hi => hs i (Finset.mem_insert_of_mem hi))
      (fun i hi j hj => hc i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj))
    have hmem : p a • x ∈ Λ := hΛ _ (GlobalTheory.SplitHomLattice.idem_int hsa) x hx
    have hhalf : IsHalf (p a) (p a • x) := fun i j => by
      rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hsa.1]
    have h1 : heisO ψ S T (p a • x) f = f := hf.2 (p a) hsa _ hmem hhalf
    have hz : hO S T (p a • x) ((∑ i ∈ s, p i) • x) = 0 := by

      rw [GlobalTheory.LatVacSign.hO_smul_smul, map_sum, Finset.mul_sum,
      Finset.sum_eq_zero (fun j hj => hc a (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)),
      zero_mul]
    have key := GlobalTheory.LatVac.heisO_heisO ψ (p a • x) ((∑ i ∈ s, p i) • x) f
    rw [ih', h1, symplOH_eq_zero_of_hO hz, ψ.map_zero_eq_one, one_smul, ← add_smul] at key
    rw [Finset.sum_insert ha]
    exact key.symm

theorem isSplitIdem_cA {e : AE D} (he : IsSplitIdem D e) : IsSplitIdem D (cA D e) := by
  obtain ⟨he1, he2, v, ε, hpl, he3⟩ := he
  exact ⟨by rw [← RingHom.map_mul, he1], by rw [GlobalTheory.LatVac.cA_cA, mul_comm, he2], v, ε, hpl,
    by rw [GlobalTheory.LatVac.cA_cA, add_comm, he3]⟩

theorem heisO_idemSum_fix : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Λ : AddSubgroup (WO S T))
    (f : WO S T → ℂ), IsLatVac (heisO ψ S T) Λ f → (∀ w : AE D, finPart D w ∈ intAE D → ∀ u ∈ Λ, w • u ∈ Λ) →
    ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ x ∈ Λ,
      heisO ψ S T (e • x) f = f ∧ heisO ψ S T (cA D e • x) f = f := by
  intro D ψ S T Λ f hf hΛ e SS he x hx
  obtain ⟨⟨es, hes, rfl⟩, hce⟩ := he
  have h1 : ∀ i ∈ SS, es i * es i = es i := fun i hi => (hes i hi).1.1
  have hcross : ∀ i ∈ SS, ∀ j ∈ SS, es i * cA D (es j) = 0 :=
    GlobalTheory.PlaceDatum.cross_eq_zero (R := AE D) GlobalTheory.PlaceDatum.isUnit_natCast (cA D) es SS h1 hce
  refine ⟨heisO_sum_smul ψ S T Λ f hf hΛ es SS (fun i hi => (hes i hi).1) hcross x hx, ?_⟩

  rw [map_sum]
  refine heisO_sum_smul ψ S T Λ f hf hΛ (fun i => cA D (es i)) SS (fun i hi => isSplitIdem_cA (hes i hi).1)
    (fun i hi j hj => ?_) x hx
  rw [← RingHom.map_mul, hcross i hi j hj, map_zero]

end GlobalTheory.IdemSumVac
end
end
