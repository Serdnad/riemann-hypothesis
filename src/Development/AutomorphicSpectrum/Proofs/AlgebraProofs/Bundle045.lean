module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle002
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle028
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle033
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle038
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle022
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle006
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle007
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LinearIndependentEigProj
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle031
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle041
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle028
public import GroundTheory.FunctionField.PlaceDefs
public import Development.WeilBound.CoreStatements.HodgeTatePoints.PlenPlaces
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle040
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle016
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness.KerFree

open GlobalTheory.CompanionTheory.Ar.Num

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem mem_dotDual_iff (R : Subalgebra o Ω) {m : ℕ} {L : AddSubgroup (Fin m → Ω)}
    {v : Fin m → Ω} : v ∈ dotDual R L ↔ ∀ l ∈ L, l ⬝ᵥ v ∈ R := by
  simp only [dotDual, AddSubgroup.mem_iInf, AddSubgroup.mem_comap]
  rfl

theorem std_le_dual (R : Subalgebra o Ω) {m : ℕ} {A : AddSubgroup (Fin m → Ω)}
    (h : A ≤ stdLat R (Fin m)) : stdLat R (Fin m) ≤ dotDual R A := by
  intro v hv
  rw [mem_dotDual_iff]
  intro l hl
  have hl' := (LatticeGoodness.mem_stdLat R).1 (h hl)
  have hv' := (LatticeGoodness.mem_stdLat R).1 hv
  show ∑ i, l i * v i ∈ R
  exact sum_mem fun i _ => R.mul_mem (hl' i) (hv' i)

theorem smul_mem_std (R : Subalgebra o Ω) {m : ℕ} {A : AddSubgroup (Fin m → Ω)} {w : Ω}
    (h : mulLat w (stdLat R (Fin m)) ≤ A) {v : Fin m → Ω} (hv : v ∈ dotDual R A) :
    w • v ∈ stdLat R (Fin m) := by
  classical
  rw [LatticeGoodness.mem_stdLat]
  intro j
  have h0 : (Pi.single j 1 : Fin m → Ω) ∈ stdLat R (Fin m) := by
    rw [LatticeGoodness.mem_stdLat]
    intro k
    by_cases hk : k = j
    · subst hk; simpa using R.one_mem
    · simpa [Pi.single_apply, hk] using R.zero_mem
  have h1 : w • (Pi.single j 1 : Fin m → Ω) ∈ A := h (AddSubgroup.mem_map.2 ⟨_, h0, rfl⟩)
  have h2 := (mem_dotDual_iff R).1 hv _ h1
  simpa [smul_dotProduct] using h2

theorem core (R : Subalgebra o Ω) {a b c : ℕ} (W : AddSubgroup (Fin a → Ω))
    (O : AddSubgroup (Fin c → Ω)) (Gam : AddSubgroup ((Fin a → Ω) × (Fin b → Ω)))
    (Del : AddSubgroup ((Fin b → Ω) × (Fin c → Ω))) (H : AddSubgroup (Fin b → Ω)) (w : Ω)
    (hw0 : w ≠ 0) (fW : LocFree R a W) (fO : LocFree R c O) (fH : LocFree R b H)
    (hstd : stdLat R (Fin b) ≤ H) (hwv : ∀ v ∈ H, w • v ∈ stdLat R (Fin b))
    (fIm : LocFree R c ((Del ⊓ H.prod ⊤).map (AddMonoidHom.snd _ _)))
    (sG : ∀ x ∈ R, ∀ v ∈ Gam, x • v ∈ Gam) (sD : ∀ x ∈ R, ∀ v ∈ Del, x • v ∈ Del)
    (g1 : ∀ x, (∃ y, (x, y) ∈ Gam) ↔ w • x ∈ W) (g2 : ∀ y, (0, y) ∈ Gam ↔ y ∈ stdLat R _)
    (g3 : ∀ x, (x, 0) ∈ Gam ↔ x ∈ W)
    (d1 : ∀ y, (∃ z, (y, z) ∈ Del) ↔ w • y ∈ stdLat R _) (d3 : ∀ z, (0, z) ∈ Del ↔ z ∈ O)
    (d4 : ∀ y, (y, 0) ∈ Del ↔ ∃ x, (x, y) ∈ Gam) :
    LocFree R a ((Gam ⊓ (⊤ : AddSubgroup _).prod H).map (AddMonoidHom.fst _ _)) := by

  have hK : LocFree R b ((Del ⊓ H.prod ⊤).comap (AddMonoidHom.inl _ _)) := by
    refine (LocFreeSchanuel.main R b c H _ O (Del ⊓ H.prod ⊤) fH fIm fO ?_ ?_ ?_ ?_ ?_).2
    · intro x hx v hv
      obtain ⟨h1, h2⟩ := AddSubgroup.mem_inf.1 hv
      refine AddSubgroup.mem_inf.2 ⟨sD x hx v h1, AddSubgroup.mem_prod.2 ⟨?_, trivial⟩⟩
      exact fH.1 x hx _ (AddSubgroup.mem_prod.1 h2).1
    · intro v z h
      exact ⟨(AddSubgroup.mem_prod.1 (AddSubgroup.mem_inf.1 h).2).1, AddSubgroup.mem_map.2 ⟨(v, z), h, rfl⟩⟩
    · intro v hv
      obtain ⟨z, hz⟩ := (d1 v).2 (hwv v hv)
      exact ⟨z, AddSubgroup.mem_inf.2 ⟨hz, AddSubgroup.mem_prod.2 ⟨hv, trivial⟩⟩⟩
    · intro z
      constructor
      · intro h
        exact (d3 z).1 (AddSubgroup.mem_inf.1 h).1
      · intro h
        exact AddSubgroup.mem_inf.2 ⟨(d3 z).2 h, AddSubgroup.mem_prod.2 ⟨H.zero_mem, trivial⟩⟩
    · intro z hz
      obtain ⟨⟨v, z'⟩, h, rfl⟩ := AddSubgroup.mem_map.1 hz
      exact ⟨v, h⟩
  have sG' : ∀ x ∈ R, ∀ v ∈ Gam ⊓ (⊤ : AddSubgroup _).prod H, x • v ∈ Gam ⊓ (⊤ : AddSubgroup _).prod H := by
    intro x hx v hv
    obtain ⟨h1, h2⟩ := AddSubgroup.mem_inf.1 hv
    exact AddSubgroup.mem_inf.2 ⟨sG x hx v h1, AddSubgroup.mem_prod.2
      ⟨trivial, fH.1 x hx _ (AddSubgroup.mem_prod.1 h2).2⟩⟩

  have hG' : LocFree R (a + b) (Gam ⊓ (⊤ : AddSubgroup _).prod H) := by
    have e1 : (Gam ⊓ (⊤ : AddSubgroup _).prod H).comap
        (LinearMap.inl Ω (Fin a → Ω) (Fin b → Ω)).toAddMonoidHom = W := by
      ext x
      constructor
      · intro h
        exact (g3 x).1 (AddSubgroup.mem_inf.1 h).1
      · intro h
        exact AddSubgroup.mem_inf.2 ⟨(g3 x).2 h, AddSubgroup.mem_prod.2 ⟨trivial, H.zero_mem⟩⟩
    have e2 : (Gam ⊓ (⊤ : AddSubgroup _).prod H).map
        (LinearMap.snd Ω (Fin a → Ω) (Fin b → Ω)).toAddMonoidHom =
        (Del ⊓ H.prod ⊤).comap (AddMonoidHom.inl _ _) := by
      ext y
      constructor
      · intro h
        obtain ⟨⟨x, y'⟩, hxy, rfl⟩ := AddSubgroup.mem_map.1 h
        obtain ⟨h1, h2⟩ := AddSubgroup.mem_inf.1 hxy
        exact AddSubgroup.mem_inf.2 ⟨(d4 y').2 ⟨x, h1⟩,
          AddSubgroup.mem_prod.2 ⟨(AddSubgroup.mem_prod.1 h2).2, trivial⟩⟩
      · intro h
        obtain ⟨h1, h2⟩ := AddSubgroup.mem_inf.1 h
        obtain ⟨x, hx⟩ := (d4 y).1 h1
        exact AddSubgroup.mem_map.2 ⟨(x, y), AddSubgroup.mem_inf.2 ⟨hx,
          AddSubgroup.mem_prod.2 ⟨trivial, (AddSubgroup.mem_prod.1 h2).1⟩⟩, rfl⟩
    exact LocFreeExt.main R (LinearMap.inl Ω _ _) (LinearMap.snd Ω _ _) LinearMap.inl_injective
      LinearMap.snd_surjective (LinearMap.range_inl Ω _ _) _ a b sG' (e1 ▸ fW) (e2 ▸ hK)

  have eF : Gam.map (LinearMap.fst Ω (Fin a → Ω) (Fin b → Ω)).toAddMonoidHom = divLat w W := by
    ext x
    constructor
    · intro h
      obtain ⟨⟨x', y⟩, hxy, rfl⟩ := AddSubgroup.mem_map.1 h
      exact (g1 x').1 ⟨y, hxy⟩
    · intro h
      obtain ⟨y, hy⟩ := (g1 x).2 h
      exact AddSubgroup.mem_map.2 ⟨(x, y), hy, rfl⟩
  have fDiv : LocFree R a (Gam.map (LinearMap.fst Ω (Fin a → Ω) (Fin b → Ω)).toAddMonoidHom) :=
    eF ▸ LatticeGoodness.locFree_divLat R hw0 fW
  have hGam : LocFree R (b + a) Gam := by
    have e1 : Gam.comap (LinearMap.inr Ω (Fin a → Ω) (Fin b → Ω)).toAddMonoidHom = stdLat R (Fin b) := by
      ext y
      exact g2 y
    exact LocFreeExt.main R (LinearMap.inr Ω _ _) (LinearMap.fst Ω _ _) LinearMap.inr_injective
      LinearMap.fst_surjective (LinearMap.range_inr Ω _ _) _ b a sG
      (e1 ▸ LatticeGoodness.locFree_stdLat R b) fDiv

  have hfin : Module.finrank Ω (LinearMap.ker (LinearMap.fst Ω (Fin a → Ω) (Fin b → Ω))) = b := by
    rw [← LinearMap.range_inr, LinearMap.finrank_range_of_inj LinearMap.inr_injective,
      Module.finrank_fin_fun]
  obtain ⟨ρ, hρ1, hρ2, hρ3⟩ := (GlobalTheory.T.locally_free_summand_criterion R (LinearMap.ker (LinearMap.fst Ω (Fin a → Ω) (Fin b → Ω)))
    (b + a) a Gam hGam).1
    ((LatticeGoodness.locFree_map_mkQ_iff R _ LinearMap.fst_surjective Gam).2 fDiv)
  have hS : Summand (Gam ⊓ (⊤ : AddSubgroup _).prod H)
      (LinearMap.ker (LinearMap.fst Ω (Fin a → Ω) (Fin b → Ω))) := by
    refine ⟨ρ, hρ1, hρ2, fun v hv => ?_⟩
    have h1 := hρ3 v (AddSubgroup.mem_inf.1 hv).1
    have h2 : (ρ v).1 = 0 := hρ1 v
    refine AddSubgroup.mem_inf.2 ⟨h1, AddSubgroup.mem_prod.2 ⟨trivial, hstd ?_⟩⟩
    apply (g2 _).1
    have : ((0 : Fin a → Ω), (ρ v).2) = ρ v := by rw [← h2]
    rwa [this]
  have hfinal := ((GlobalTheory.T.locally_free_summand_criterion R (LinearMap.ker (LinearMap.fst Ω (Fin a → Ω) (Fin b → Ω)))
    (a + b) a _ hG').2 hS).2
  rw [hfin, Nat.add_sub_cancel] at hfinal
  exact (LatticeGoodness.locFree_map_mkQ_iff R _ LinearMap.fst_surjective _).1 hfinal

theorem main : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → D.Good₁ R p χ → D.Good₂ R p χ → (∀ τ, mulLat w (stdLat R _) ≤ D.af R p (χ τ)) → ∀ τ, LocFree R (r τ) (D.kerH R p τ (χ τ)) := by
  intro o Ω _ _ _ F _ _ _ n Sg r s D R p w χ hC hB hG₁ hG₂ hw τ
  have hw0 : w ≠ 0 := by
    obtain ⟨c, -, hc⟩ := hC.2.2.1
    intro h
    apply hC.1
    rw [hc, h, mul_zero]
  obtain ⟨-, fH, hle, -⟩ := (GlobalTheory.T.lattice_good_base_change D R p w χ hC hB hG₁).1 τ
  obtain ⟨-, fW, -, fO⟩ := hB.free τ
  obtain ⟨g1, g2, g3⟩ := hB.gam τ
  obtain ⟨d1, -, d3, d4⟩ := hB.del τ
  exact core R (D.W τ) (D.omHT τ) (D.Gam τ) (D.Del τ) (D.hh R p (χ τ)) w hw0 fW fO fH
    (std_le_dual R hle) (fun v hv => smul_mem_std R (hw τ) hv) (hG₂.im τ)
    (fun x hx => (hB.stable τ x hx).1) (fun x hx => (hB.stable τ x hx).2.1) g1 g2 g3 d1 d3 d4

end GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness.KerFree
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness.StepIdeal

open GlobalTheory.CompanionTheory.Ar.Num

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem mem_annSub_iff {n k : ℕ} {v : Fin n → Ω} :
    v ∈ annSub Ω n k ↔ ∀ j : Fin n, (j : ℕ) < k → v j = 0 := by
  simp [annSub, Submodule.mem_pi]

def stepCoord (Ω : Type) [Field Ω] {n : ℕ} (i : Fin n) : annSub Ω n i →ₗ[Ω] Ω :=
  (LinearMap.proj i).comp (annSub Ω n i).subtype

theorem stepCoord_apply {n : ℕ} (i : Fin n) (v : annSub Ω n i) :
    stepCoord Ω i v = (v : Fin n → Ω) i := rfl

theorem stepCoord_surjective {n : ℕ} (i : Fin n) : Function.Surjective (stepCoord Ω i) := by
  classical
  intro c
  refine ⟨⟨Pi.single i c, mem_annSub_iff.2 fun j hj => ?_⟩, by simp [stepCoord_apply]⟩
  have : j ≠ i := by rintro rfl; exact lt_irrefl _ hj
  simp [Pi.single_apply, this]

theorem mem_ker_stepCoord {n : ℕ} (i : Fin n) (v : annSub Ω n i) :
    v ∈ LinearMap.ker (stepCoord Ω i) ↔ (v : Fin n → Ω) ∈ annSub Ω n ((i : ℕ) + 1) := by
  rw [LinearMap.mem_ker, stepCoord_apply, mem_annSub_iff]
  constructor
  · intro h j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
    · exact mem_annSub_iff.1 v.2 j hj
    · rw [Fin.ext hj]; exact h
  · intro h
    exact h i (Nat.lt_succ_self _)

theorem summand_step {n : ℕ} {L : AddSubgroup (Fin n → Ω)} (i : Fin n)
    (h : Summand L (annSub Ω n ((i : ℕ) + 1))) :
    Summand (L.comap (annSub Ω n i).subtype.toAddMonoidHom) (LinearMap.ker (stepCoord Ω i)) := by
  obtain ⟨ρ, h1, h2, h3⟩ := h
  have hle : ∀ v, ρ v ∈ annSub Ω n i := fun v =>
    mem_annSub_iff.2 fun j hj => mem_annSub_iff.1 (h1 v) j (Nat.lt_succ_of_lt hj)
  refine ⟨(ρ.comp (annSub Ω n i).subtype).codRestrict _ fun v => hle _, fun v => ?_, fun u hu => ?_,
    fun v hv => ?_⟩
  · rw [mem_ker_stepCoord]
    exact h1 _
  · apply Subtype.ext
    exact h2 _ ((mem_ker_stepCoord i u).1 hu)
  · exact h3 _ hv

theorem locFree_step (R : Subalgebra o Ω) {n : ℕ} {L : AddSubgroup (Fin n → Ω)} (hL : LocFree R n L)
    (i : Fin n) (h₀ : Summand L (annSub Ω n i)) (h₁ : Summand L (annSub Ω n ((i : ℕ) + 1))) :
    LocFree R 1 ((L ⊓ (annSub Ω n i).toAddSubgroup).map (Pi.evalAddMonoidHom (fun _ => Ω) i)) := by
  have hA := ((GlobalTheory.T.locally_free_summand_criterion R (annSub Ω n i) n 0 L hL).2 h₀).1
  have hB := ((GlobalTheory.T.locally_free_summand_criterion R (LinearMap.ker (stepCoord Ω i)) _ 0 _ hA).2 (summand_step i h₁)).2
  have hr : Module.finrank Ω (annSub Ω n i) - Module.finrank Ω (LinearMap.ker (stepCoord Ω i)) = 1 := by
    have h := LinearMap.finrank_range_add_finrank_ker (stepCoord Ω i)
    rw [LinearMap.range_eq_top.2 (stepCoord_surjective i), finrank_top, Module.finrank_self] at h
    omega
  rw [hr] at hB
  have hC := (locFree_map_mkQ_iff R (stepCoord Ω i) (stepCoord_surjective i) _).1 hB
  convert hC using 1
  ext c
  constructor
  · rintro ⟨v, ⟨hv, hv'⟩, rfl⟩
    exact ⟨⟨v, hv'⟩, hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, ⟨hv, v.2⟩, rfl⟩

theorem main : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → D.Good₁ R p χ → D.Good₂ R p χ → (∀ τ i, LocFree R 1 (D.dId R p (χ τ) i)) ∧ ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → ∀ τ i, (D.bc RC).dId RC p (fun a => algebraMap Ω C (χ τ a)) i = spanOver RC (algebraMap Ω C '' D.dId R p (χ τ) i) := by
  intro o Ω _ _ _ F _ _ _ n Sg r s D R p w χ hc hB h1 h2
  obtain ⟨hg, hbc⟩ := GlobalTheory.T.lattice_good_base_change D R p w χ hc hB h1
  refine ⟨fun τ i => locFree_step R (hg τ).1 i (h2.ann τ i) (h2.ann τ ((i : ℕ) + 1)), ?_⟩
  intro C _ _ _ _ RC hRC τ i
  have haf := ((hbc C RC hRC).2 τ).1
  have hs := (GlobalTheory.T.locally_free_base_change_summand R RC hRC (bcMap Ω C (Fin n)) (isBaseChange_bcMap Ω C _)
    (D.af R p (χ τ)) (annSub Ω n i) (hg τ).1.1 (h2.ann τ i)).2
  rw [span_bcMap_annSub] at hs
  unfold LieLatticeData.dId
  rw [haf, hs]
  have hm := SpanExact.map_spanOver RC
    (bcMap Ω C (Fin n) '' ((D.af R p (χ τ) ⊓ (annSub Ω n i).toAddSubgroup : AddSubgroup _) : Set (Fin n → Ω)))
    (LinearMap.proj i : (Fin n → C) →ₗ[C] C)
  have himg : algebraMap Ω C '' (((D.af R p (χ τ) ⊓ (annSub Ω n i).toAddSubgroup : AddSubgroup _).map
      (Pi.evalAddMonoidHom (fun _ => Ω) i) : AddSubgroup Ω) : Set Ω) =
      (LinearMap.proj i : (Fin n → C) →ₗ[C] C) '' (bcMap Ω C (Fin n) ''
        ((D.af R p (χ τ) ⊓ (annSub Ω n i).toAddSubgroup : AddSubgroup _) : Set (Fin n → Ω))) := by
    ext c
    constructor
    · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨_, ⟨v, hv, rfl⟩, rfl⟩
  rw [himg, ← hm]
  rfl

end GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness.StepIdeal
end
end

section

open scoped NNReal
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Flat.ExG

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ExG.SumEig

theorem sum_embeddings_eq_trace (E : Type) [Field E] [NumberField E] (C : Type) [Field C] [CharZero C]
    [Fintype (E →+* C)] (hc : Fintype.card (E →+* C) = Module.finrank ℚ E) (x : E) :
    ∑ s : E →+* C, s x = algebraMap ℚ C (Algebra.trace ℚ E x) := by
  classical
  let Ω := AlgebraicClosure C
  let f : (E →+* C) → (E →ₐ[ℚ] Ω) := fun s => RingHom.toRatAlgHom ((algebraMap C Ω).comp s)
  have hf : ∀ s y, f s y = algebraMap C Ω (s y) := fun s y => rfl
  have hinj : Function.Injective f := by
    intro s t hst
    ext y
    have h := congrArg (fun φ : E →ₐ[ℚ] Ω => φ y) hst
    simp only [hf] at h
    exact (algebraMap C Ω).injective h
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hinj, by rw [hc, AlgHom.card]⟩
  have key : algebraMap ℚ Ω (Algebra.trace ℚ E x) = ∑ σ : E →ₐ[ℚ] Ω, σ x :=
    trace_eq_sum_embeddings Ω (x := x)
  rw [← hbij.sum_comp (fun σ : E →ₐ[ℚ] Ω => σ x)] at key
  simp only [hf] at key
  apply (algebraMap C Ω).injective

  rw [map_sum, ← key, eq_ratCast (algebraMap ℚ Ω), eq_ratCast (algebraMap ℚ C), map_ratCast]

theorem sum_eigProj (E : Type) [Field E] [NumberField E] (C : Type) [Field C] [CharZero C]
    [Fintype (E →+* C)] (hc : Fintype.card (E →+* C) = Module.finrank ℚ E)
    (M : Type) [AddCommGroup M] [Module C M] (ρ : 𝓞 E →+* Module.End C M) (y : M) :
    ∑ s, HT.eigProj ρ s y = y := by
  classical
  set b := RingOfIntegers.basis E with hb
  have h1 : (1 : E) = ∑ j, ((b.repr 1 j : ℤ) : ℚ) • integralBasis E j := by
    calc (1 : E) = algebraMap (𝓞 E) E 1 := (map_one _).symm
      _ = algebraMap (𝓞 E) E (∑ j, b.repr 1 j • b j) := by rw [b.sum_repr]
      _ = ∑ j, ((b.repr 1 j : ℤ) : ℚ) • integralBasis E j := by

        rw [map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [integralBasis_apply, map_zsmul, Int.cast_smul_eq_zsmul]
  have htr : ∀ k, Algebra.trace ℚ E (HT.dualInt E k) = ((b.repr 1 k : ℤ) : ℚ) := by
    intro k
    calc Algebra.trace ℚ E (HT.dualInt E k) = Algebra.traceForm ℚ E (HT.dualInt E k) 1 := by
          rw [Algebra.traceForm_apply, mul_one]
      _ = ∑ j, ((b.repr 1 j : ℤ) : ℚ) * Algebra.traceForm ℚ E (HT.dualInt E k) (integralBasis E j) := by
          conv_lhs => rw [h1]

          rw [map_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_smul, smul_eq_mul]
      _ = ((b.repr 1 k : ℤ) : ℚ) := by
          simp only [HT.dualInt, LinearMap.BilinForm.apply_dualBasis_left, mul_ite, mul_one, mul_zero,
            Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hsum : ∀ k, ∑ s : E →+* C, s (HT.dualInt E k) = ((b.repr 1 k : ℤ) : C) := by
    intro k
    rw [sum_embeddings_eq_trace E C hc, htr, map_intCast]
  calc ∑ s, HT.eigProj ρ s y = ∑ s : E →+* C, ∑ k, s (HT.dualInt E k) • ρ (b k) y := by
        refine Finset.sum_congr rfl fun s _ => ?_
        simp only [HT.eigProj]
        rw [LinearMap.sum_apply]
        simp only [LinearMap.smul_apply, hb]
    _ = ∑ k, (∑ s : E →+* C, s (HT.dualInt E k)) • ρ (b k) y := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_smul]
    _ = ∑ k, ((b.repr 1 k : ℤ) : C) • ρ (b k) y := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hsum]
    _ = ρ (∑ k, b.repr 1 k • b k) y := by

        rw [map_sum, LinearMap.sum_apply]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [map_zsmul, LinearMap.smul_apply, Int.cast_smul_eq_zsmul]
    _ = y := by
        rw [b.sum_repr, map_one, Module.End.one_apply]

end GlobalTheory.CompanionTheory.Ar.Flat.ExG.SumEig
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.hermitian_signature_basis : ∀ (E : Type) [Field E] [NumberField E] (K W : Type) [Field K] [CharZero K] [AddCommGroup W] [Module K W] [FiniteDimensional K W] (ρ : 𝓞 E →+* Module.End K W) (ρH : 𝓞 E →+* Module.End K (W × Module.Dual K W)) (bar : 𝓞 E ≃+* 𝓞 E) (σ σ' : E →+* K) (p q : ℕ) (v : Fin p → W) (w : Fin q → W), (∀ a y, (ρH a y).1 = ρ a y.1) → (∀ a φ, ρH a (0, φ) = (0, φ ∘ₗ ρ (bar a))) → (∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) → (∀ a, bar (bar a) = a) → LinearIndependent K v → Submodule.span K (Set.range v) = HT.eigSp ρ σ → LinearIndependent K w → Submodule.span K (Set.range w) = HT.eigSp ρ σ' → ∃ u, IsAdapted ρH σ v w u ∧ LinearIndependent K u ∧ Submodule.span K (Set.range u) = HT.eigSp ρH σ :=
  @_root_.PositivityTheory.Xgn.adapted_eigenbasis_exists
end

section

set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal


theorem _root_.GlobalTheory.T.fibre_count_rotation_invariant : ∀ (n e : ℕ) (S : Set (EuclideanSpace ℂ (Fin n))), IsScaleStable S →
  ∀ (w : EuclideanSpace ℂ (Fin (e + 1))), w ≠ 0 → ∀ T : ℝ≥0∞ → ℝ≥0∞,
    ∫⁻ π : Fin (e + 1) → Fin n → ℂ, matGauss π * T (cntOver S π w) =
      ∫⁻ π : Fin (e + 1) → Fin n → ℂ, matGauss π * T (cntOver S π (firstCoordVec (e + 1))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Short.Crofton.CntInv.lintegral_matGauss_cntOver | exact GlobalTheory.CompanionTheory.Ar.Short.Crofton.CntInv.lintegral_matGauss_cntOver | (intros; apply GlobalTheory.CompanionTheory.Ar.Short.Crofton.CntInv.lintegral_matGauss_cntOver <;> assumption)
end

section

set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal


theorem _root_.GlobalTheory.T.gaussian_matrix_measure_pos_finite : ∀ m n : ℕ, 0 < gaussM m n Set.univ ∧ gaussM m n Set.univ < ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Short.Crofton.gaussM_univ_pos_lt_top | exact GlobalTheory.CompanionTheory.Ar.Short.Crofton.gaussM_univ_pos_lt_top | (intros; apply GlobalTheory.CompanionTheory.Ar.Short.Crofton.gaussM_univ_pos_lt_top <;> assumption)
end

section

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

theorem _root_.GlobalTheory.T.hodge_tate_constant_divides_p_sq : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) [CharZero C] (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [IsDomain A] [CharZero A] (φ : A →+* O) (κ : A), v (p : C) < 1 → (if p = 2 then κ = 4 else ∃ ζ : A, IsPrimitiveRoot ζ p ∧ κ = ζ - 1) → IsHTConst v p (φ κ) ∧ κ ∣ (p : A) ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.isHTConst_of_isCp | exact GlobalTheory.CompanionTheory.Ar.HT.isHTConst_of_isCp | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.isHTConst_of_isCp <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem free_on_lift : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (La : Type) [AddCommGroup La] [Module (𝓞 E) La] (EF : La →ₗ[ℤ] La →ₗ[ℤ] ℤ) (N : ℕ) (u : Fin N → La), IsPolLattice c p EF u → ∃ (ρ : 𝓞 E →+* Module.End C (C ⊗[ℤ] La)) (T : Submodule O (C ⊗[ℤ] La)) (e : C ⊗[ℤ] La →ₗ[C] C ⊗[ℤ] La →ₗ[C] C), (∀ (a : 𝓞 E) (x : La), ρ a (1 ⊗ₜ x) = 1 ⊗ₜ (a • x)) ∧ T = Submodule.span O (Set.range fun x : La => (1 : C) ⊗ₜ[ℤ] x) ∧ IsFreeOn ρ T (fun i => 1 ⊗ₜ u i) ∧ (∀ x y : La, e (1 ⊗ₜ x) (1 ⊗ₜ y) = (EF x y : C)) ∧ (∀ x, e x x = 0) ∧ (∀ y, (∀ x, e x y = 0) → y = 0) ∧ dualLat e T = T ∧ ∀ (a : 𝓞 E) x y, e (ρ a x) y = e x (ρ (RingOfIntegers.mapRingEquiv c a) y) :=
  @PositivityTheory.HtPt.Gi.free_on_lift

end GlobalTheory.CompanionTheory.Ar.HT
end

section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

theorem _root_.GlobalTheory.CompanionTheory.Relay.length_formula_sum_valuations : ∀ (k K A : Type) [Field k] [Field K] [Algebra k K] [GroundTheory.FunctionField.IsFunctionField k K] [CommRing A] [IsDomain A] [Algebra k A] [Algebra A K] [IsScalarTower k A K] [IsLocalRing A] [IsNoetherianRing A] [IsFractionRing A K] [Algebra.EssFiniteType k A], ¬ IsField A → ∀ f : A, f ≠ 0 → (((Module.length A (A ⧸ Ideal.span {f})).toNat * Module.finrank k (IsLocalRing.ResidueField A) : ℕ) : ℤ) = ∑ᶠ v ∈ {v : GroundTheory.FunctionField.Place k K | (∀ a : A, v.valuation (algebraMap A K a) ≤ 1) ∧ ∀ a ∈ IsLocalRing.maximalIdeal A, v.valuation (algebraMap A K a) < 1}, (v.deg : ℤ) * v.ord (algebraMap A K f) := by
  first | exact @PositivityTheory.HtPt.Plen.len_places | exact PositivityTheory.HtPt.Plen.len_places
end
