module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1514
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1709
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.DetOfCharpoly
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapQrOneBijective
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.RootSumWOff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
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
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PerCApply
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

namespace UpperTheory.Gal.W2.FrobeniusTrace

variable {p : ℕ} [Fact p.Prime]

private theorem not_both (G : HTGroup p) (τ : G.F →+* PadicAlgCl p) (h1 : LiesOver G.Kq G.u τ)
    (h2 : LiesOver G.Kq G.u (τ.comp (IsCMField.complexConj G.F : G.F →+* G.F))) : False := by
  obtain ⟨x, hx, hne⟩ := CentAtP.exists_conj_ne G
  apply hne
  apply τ.injective
  have a := h1 ⟨x, hx⟩
  have b := h2 ⟨x, hx⟩
  exact b.trans a.symm

private theorem exists_ext (E : IntermediateField ℚ_[p] (PadicAlgCl p))
    (s : E →ₐ[ℚ_[p]] PadicAlgCl p) :
    ∃ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, ∀ y : E, σ (y : PadicAlgCl p) = s y := by
  obtain ⟨φ, hφ⟩ := IntermediateField.exists_algHom_of_splits
    (fun z => ⟨Algebra.IsIntegral.isIntegral z, IsAlgClosed.splits _⟩) s
  refine ⟨AlgEquiv.ofBijective φ (Algebra.IsAlgebraic.algHom_bijective φ), fun y => ?_⟩
  rw [AlgEquiv.ofBijective_apply]
  exact congrArg (fun f => f y) hφ

private theorem hom_ext {F : Type} [Field F] (τ : F →+* PadicAlgCl p)
    (s s' : FwOf τ →ₐ[ℚ_[p]] PadicAlgCl p) (h : ∀ x, s (embOf τ x) = s' (embOf τ x)) : s = s' := by
  refine IntermediateField.algHom_ext_of_eq_adjoin ℚ_[p]
    (rfl : FwOf τ = IntermediateField.adjoin ℚ_[p] (Set.range τ)) ?_
  rintro _ ⟨x, rfl⟩
  exact h x

private theorem sigma_eq (G : HTGroup p) {w w' : Fin G.m} (s : G.Fw w →ₐ[ℚ_[p]] PadicAlgCl p)
    (s' : G.Fw w' →ₐ[ℚ_[p]] PadicAlgCl p) (h : ∀ x, s (G.embW w x) = s' (G.embW w' x)) :
    (⟨w, s⟩ : Σ w, G.Fw w →ₐ[ℚ_[p]] PadicAlgCl p) = ⟨w', s'⟩ := by
  obtain ⟨σ, hσ⟩ := exists_ext _ s
  obtain ⟨σ', hσ'⟩ := exists_ext _ s'
  have hw : w = w' := by
    refine G.emb_inj w w' (σ.trans σ'.symm) (RingHom.ext fun x => ?_)
    have e1 : σ (G.emb w x) = s (G.embW w x) := hσ (G.embW w x)
    have e2 : σ' (G.emb w' x) = s' (G.embW w' x) := hσ' (G.embW w' x)
    change σ'.symm (σ (G.emb w x)) = G.emb w' x
    rw [e1, h, ← e2, AlgEquiv.symm_apply_apply]
  subst hw
  rw [hom_ext (G.emb w) s s' h]

private theorem liesOver_comp (G : HTGroup p) {w : Fin G.m} (s : G.Fw w →ₐ[ℚ_[p]] PadicAlgCl p) :
    LiesOver G.Kq G.u ((s : G.Fw w →+* PadicAlgCl p).comp (G.embW w)) := by
  intro x
  have e : G.embW w (x : G.F) = algebraMap ℚ_[p] (G.Fw w) (G.u x) := Subtype.ext (G.emb_over w x)
  change s (G.embW w (x : G.F)) = _
  rw [e, s.commutes]

private noncomputable def phi (G : HTGroup p) :
    ((Σ w, G.Fw w →ₐ[ℚ_[p]] PadicAlgCl p) ⊕ (Σ w, G.Fw w →ₐ[ℚ_[p]] PadicAlgCl p)) →
      (G.F →ₐ[ℚ] PadicAlgCl p)
  | .inl a => ((a.2 : G.Fw a.1 →+* PadicAlgCl p).comp (G.embW a.1)).toRatAlgHom
  | .inr a => ((a.2 : G.Fw a.1 →+* PadicAlgCl p).comp
      ((G.embW a.1).comp (IsCMField.complexConj G.F : G.F →+* G.F))).toRatAlgHom

private theorem phi_inl (G : HTGroup p) (a : Σ w, G.Fw w →ₐ[ℚ_[p]] PadicAlgCl p) (x : G.F) :
    phi G (.inl a) x = a.2 (G.embW a.1 x) := rfl

private theorem phi_inr (G : HTGroup p) (a : Σ w, G.Fw w →ₐ[ℚ_[p]] PadicAlgCl p) (x : G.F) :
    phi G (.inr a) x = a.2 (G.embW a.1 (IsCMField.complexConj G.F x)) := rfl

private theorem phi_ne (G : HTGroup p) (a b : Σ w, G.Fw w →ₐ[ℚ_[p]] PadicAlgCl p) :
    phi G (.inl a) ≠ phi G (.inr b) := by
  intro h
  refine not_both G _ (liesOver_comp G a.2) fun k => ?_
  have e := DFunLike.congr_fun h (IsCMField.complexConj G.F (k : G.F))
  rw [phi_inl, phi_inr, IsCMField.complexConj_apply_apply] at e
  exact e.trans (liesOver_comp G b.2 k)

private theorem phi_injective (G : HTGroup p) : Function.Injective (phi G) := by
  rintro (⟨w, s⟩ | ⟨w, s⟩) (⟨w', s'⟩ | ⟨w', s'⟩) hab
  · rw [sigma_eq G s s' fun x => (phi_inl G ⟨w, s⟩ x).symm.trans
      ((DFunLike.congr_fun hab x).trans (phi_inl G ⟨w', s'⟩ x))]
  · exact absurd hab (phi_ne G _ _)
  · exact absurd hab.symm (phi_ne G _ _)
  · have key : ∀ y, s (G.embW w y) = s' (G.embW w' y) := by
      intro y
      have e := (phi_inr G ⟨w, s⟩ (IsCMField.complexConj G.F y)).symm.trans
        ((DFunLike.congr_fun hab _).trans (phi_inr G ⟨w', s'⟩ _))
      rwa [IsCMField.complexConj_apply_apply] at e
    rw [sigma_eq G s s' key]

private theorem phi_surjective (hE : EmbAll) (G : HTGroup p) : Function.Surjective (phi G) := by
  intro ψ
  obtain ⟨w, σ, h | h⟩ := hE p G ψ.toRingHom
  · refine ⟨.inl ⟨w, σ.toAlgHom.comp (G.Fw w).val⟩, AlgHom.ext fun x => ?_⟩
    rw [phi_inl]
    exact (h x).symm
  · refine ⟨.inr ⟨w, σ.toAlgHom.comp (G.Fw w).val⟩, AlgHom.ext fun x => ?_⟩
    rw [phi_inr]
    exact (h x).symm

end UpperTheory.Gal.W2.FrobeniusTrace

open UpperTheory.Gal.W2.FrobeniusTrace in
theorem UpperTheory.Gal.W2.fTrace_of :
    UpperTheory.Gal.W2.EmbAll → UpperTheory.Gal.W2.FTrace := by
  intro hE p _ G x
  apply (algebraMap ℚ_[p] (PadicAlgCl p)).injective

  rw [map_add (f := _), map_sum, map_sum]
  have hl : algebraMap ℚ_[p] (PadicAlgCl p) ((Algebra.trace ℚ G.F x : ℚ) : ℚ_[p])
      = algebraMap ℚ (PadicAlgCl p) (Algebra.trace ℚ G.F x) := by
    simp only [map_ratCast, eq_ratCast]
  rw [hl]
  simp_rw [trace_eq_sum_embeddings (E := PadicAlgCl p)]
  rw [← Fintype.sum_bijective (phi G) ⟨phi_injective G, phi_surjective hE G⟩
    (fun a => phi G a x) (fun σ => σ x) (fun _ => rfl)]
  rw [Fintype.sum_sum_type, Fintype.sum_sigma, Fintype.sum_sigma]
  simp only [phi_inl, phi_inr]
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem mem_intK_iff {p : ℕ} [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (a : K) :
    a ∈ GlobalTheory.LKLoc.intK p K ↔ ‖(a : PadicAlgCl p)‖ ≤ 1 := by
  show (algebraMap K (PadicAlgCl p) a) ∈ ReciprocityTheory.DiscreteGroups.LocalClassField.Obar p ↔ _
  exact ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Obar_iff

theorem UpperTheory.Gal.W2.kpMem_of :
    UpperTheory.Gal.W2.KpMem := by
  intro p _ G g
  rw [GlobalTheory.HeckeP.inclG_mem_KHT_iff]
  unfold UpperTheory.Gal.W2.IntPt
  have hunit : (‖(g.1 : ℚ_[p])‖ ≤ 1 ∧ ‖((g.1⁻¹ : ℚ_[p]ˣ) : ℚ_[p])‖ ≤ 1) ↔ ‖(g.1 : ℚ_[p])‖ = 1 := by
    rw [Units.val_inv_eq_inv_val, norm_inv]
    have hpos : 0 < ‖(g.1 : ℚ_[p])‖ := norm_pos_iff.2 g.1.ne_zero
    constructor
    · rintro ⟨h1, h2⟩
      exact le_antisymm h1 (by simpa using (inv_le_one₀ hpos).1 h2)
    · intro h
      rw [h]
      simp
  rw [hunit]
  apply and_congr_right'
  apply forall_congr'
  intro w
  unfold GlobalTheory.LKLoc.KintK
  rw [GlobalTheory.HeckeP.mem_range_map_subtype]
  simp only [mem_intK_iff]
  rw [← forall_and]
  apply forall_congr'
  intro i
  rw [← forall_and]
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.pkTop_of :
    UpperTheory.Gal.W2.PFrameEx → UpperTheory.Gal.W2.PkLat → UpperTheory.Gal.W2.PkEquiv → UpperTheory.Gal.W2.PkPerf → UpperTheory.Gal.W2.PkInj → UpperTheory.Gal.W2.PkOnto → UpperTheory.Gal.W2.KpMem → UpperTheory.Gal.W2.PDicEx := by
  intro hF hLat hEq hPerf hInj hOnto hKp p _ D G L _ hm B
  obtain ⟨A⟩ := hF p D G L hm B.β B.sym
  let i : Gp G ≃* Gr G 1 := MulEquiv.ofBijective (inclG G 1) (GlobalTheory.TorCls.AtP.inclG_one_bijective G)
  have hi : ∀ g, i g = inclG G 1 g := fun _ => rfl
  choose M hM hMl using hLat p D G L B.β A hm
  refine ⟨{ lat := fun hp => M (i.symm hp), isLat := fun hp => hMl _, perf := ?_, equiv := ?_, inj := ?_, onto := ?_ }⟩
  · intro hp
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    have hp1 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    set g := i.symm hp with hg
    set v : ℤ := (g.1 : ℚ_[p]).valuation with hv
    refine ⟨(p : ℚ) ^ (-v), zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _, ?_⟩
    refine hPerf p D G L B.β A g _ ?_ _ (hM g)
    have hne : (g.1 : ℚ_[p]) ≠ 0 := g.1.ne_zero
    rw [norm_mul, Padic.norm_eq_zpow_neg_valuation hne, ← hv]
    push_cast
    rw [norm_zpow, Padic.norm_p, inv_zpow', neg_neg, ← zpow_add₀ hp1.ne']
    simp
  · intro y hp w
    have e : i.symm (GlobalTheory.LKCx.toP1 G B.β y * hp) = locC G (y : G.Cˣ × ℚˣ) * i.symm hp := by
      rw [map_mul]
      congr 1
      exact i.symm_apply_apply (locC G (y : G.Cˣ × ℚˣ))
    change actY L y w ∈ M (i.symm (GlobalTheory.LKCx.toP1 G B.β y * hp)) ↔ w ∈ M (i.symm hp)
    rw [e, hM, hM]
    exact hEq p D G L B.β A y _ w
  · intro hp hp'
    have e : hp⁻¹ * hp' = inclG G 1 ((i.symm hp)⁻¹ * i.symm hp') := by
      rw [← hi, map_mul, map_inv, i.apply_symm_apply, i.apply_symm_apply]
    change M (i.symm hp) = M (i.symm hp') ↔ _
    rw [e, hKp p G, ← hInj p D G L B.β A]
    constructor
    · intro h x
      rw [← hM, ← hM, h]
    · intro h
      ext x
      rw [hM, hM]
      exact h x
  · rintro N hN ⟨s, hs, hP⟩
    obtain ⟨g, hg⟩ := hOnto p D G L B.β A hm N s hN hs hP
    refine ⟨i g, ?_⟩
    change M (i.symm (i g)) = N
    rw [i.symm_apply_apply]
    ext x
    rw [hM, hg]
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem list_prod_ofFn_eq_of_eq_one_of_ne' {M : Type*} [Monoid M] :
    ∀ {m : ℕ} (f : Fin m → M) (i : Fin m), (∀ j, j ≠ i → f j = 1) → (List.ofFn f).prod = f i := by
  intro m
  induction m with
  | zero => intro f i; exact i.elim0
  | succ m ih =>
    intro f i hf
    rw [List.ofFn_succ, List.prod_cons]
    refine Fin.cases ?_ (fun i' => ?_) i hf
    · intro hf0
      rw [List.prod_eq_one, _root_.mul_one]
      intro x hx
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
      exact hf0 _ (Fin.succ_ne_zero j)
    · intro hfs
      rw [hfs 0 (Fin.succ_ne_zero i').symm, _root_.one_mul]
      exact ih (fun j => f j.succ) i' (fun j hj => hfs _ (fun h => hj (Fin.succ_injective _ h)))

private theorem matEnd_diagonal_pr {S : Scheme.{0}} {O : Type} [Ring O] {A : Over S} [GrpObj A] (act : OActN O A) {m : ℕ}
    (d : Fin m → O) (i : Fin m) :
    GlobalTheory.KS.matEnd act (Matrix.diagonal d) ≫ GlobalTheory.KS.pr A i = GlobalTheory.KS.pr A i ≫ act.act (d i) := by
  unfold GlobalTheory.KS.matEnd GlobalTheory.KS.pr
  rw [Pi.lift_comp_π]
  rw [list_prod_ofFn_eq_of_eq_one_of_ne' _ i]
  · simp
  · intro j hj
    simp [Matrix.diagonal_apply_ne' d hj, GlobalTheory.KS.Model.act_zero, Hom.one_def]

theorem UpperTheory.Gal.W2.pwOver_of :
    UpperTheory.Gal.W2.PwOver := by
  intro p _ D G L gb N N' h X X' c k
  have hpw : c.pw k ≫ (KS.pow X.univ.A k).hom = (KS.pow X'.univ.A k).hom ≫ c.q := by
    delta Leg.pw
    exact KS.Model.powMap_over _ _ _ k
  have hpr : ∀ i : Fin k,
      c.pw k ≫ Over.Hom.left (KS.pr X.univ.A i) = Over.Hom.left (KS.pr X'.univ.A i) ≫ c.tot := by
    intro i
    delta Leg.pw
    exact KS.Model.powMap_pr _ _ _ k i
  refine ⟨hpw, hpr, ?_, fun α => ⟨?_, fun i => ?_⟩⟩
  · intro b
    delta Leg.tot
    have h1 := congrArg Over.Hom.left (c.tr.2.1 b)
    simp only [Over.comp_left] at h1
    rw [← Category.assoc, h1, Category.assoc, c.φ.act b, Category.assoc]
  · delta Leg.tw
    rw [Category.assoc, Over.w, hpw]
  · have hm := congrArg Over.Hom.left
      (matEnd_diagonal_pr X.univ.act (fun s => (algebraMap (𝓞 D.F) D.O (α s) : D.toG.O)) i)
    rw [Over.comp_left, Over.comp_left] at hm
    delta Leg.tw
    refine (Category.assoc _ _ _).trans ((congrArg (c.pw k ≫ ·) hm).trans ?_)
    rw [← Category.assoc, hpr, Category.assoc]
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem kap_inv {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (v : InfinitePlace G.F)
    (t₀ : D.F →+* ℂ) (z : ℂ) : kap L v t₀ z⁻¹ = (kap L v t₀ z)⁻¹ := by
  unfold kap
  split_ifs <;> simp

theorem UpperTheory.Gal.W2.fixLoc_of :
    UpperTheory.Gal.W2.SheetOf → UpperTheory.Gal.W2.FixGa → UpperTheory.Gal.W2.FixEq → UpperTheory.Gal.W2.OneAt → UpperTheory.Gal.W2.PowCorr → UpperTheory.Gal.W2.CspDim → UpperTheory.Gal.W2.AdExists → UpperTheory.Gal.W2.EigTop → UpperTheory.Gal.W2.LocSum → UpperTheory.Gal.W2.RegSep → UpperTheory.Gal.W2.InvMin → UpperTheory.Gal.W2.MinBridge → UpperTheory.Gal.W2.CorrChart → UpperTheory.Gal.W2.PtFibre → UpperTheory.Gal.W2.FixLoc := by
  intro hSheet hFixGa hFixEq hOneAt hPow hCsp hAd hEig hLoc hRegSep hInvMin hMinB hChart hPt
  intro p _ D G L ha hm v hv t₀ ht gb N N' h hlev X X' c₁ c₂ hX hL hX' hL' ρ hfine hsig hsm hreg U B PD RD i P j a hper hco y hsees k α hα h₁ h₂
  have hFM : FullMark N' (U.Di i) (U.t i) := by
    obtain ⟨⟨f, ν, hft, -, hn⟩, -⟩ := U.mem i
    intro x
    obtain ⟨a', e', hx⟩ := (hn N' (by have := hlev.2.2.1; omega) hlev.2.2.2.1).2.2.2.1 x
    exact ⟨a', e', by rw [hft]; exact hx⟩
  obtain ⟨S, hSu, hSex⟩ := hSheet D.O D.inv D.g ρ D.La (gfamD X' hX' hL') N' (D.Cls N') U i hlev.2.2.1 hFM
  have hUA := U.unif i P hper
  obtain ⟨ga, H, hga, hfix, hHQ⟩ := hFixGa p D G L gb N N' h hlev X X' c₁ c₂ hX hL hX' hL' ρ hfine v t₀ B PD RD (U.Di i) (U.t i) (U.mem i) P j a hco (U.u i P) (U.ex i P) hUA y hsees
  obtain ⟨Hm, hHm1, hHm2, hHm3⟩ := hper.2.2.2.2
  have hHerm : IsHermOf (U.Di i) P Hm := ⟨hHm1, hHm2, hHm3⟩
  obtain ⟨co, hcoC⟩ := hCsp D.F D.O D.inv D.g ρ (algebraMap (𝓞 D.F) D.O) D.n t₀ (epsD D) hsig (U.Di i) P Hm hper hHerm
  obtain ⟨hHdet, hHcomm, hHCsp⟩ := hAd D.O D.inv D.g ρ (U.Di i) P Hm hper hHerm ga H hfix
  let φ : (Fin (D.n - 1) → ℂ) →ₗ[ℂ] Matrix (Fin D.g) (Fin D.g) ℂ :=
    (LinearMap.mulRight ℂ (H.map star)⁻¹ ∘ₗ LinearMap.mulLeft ℂ H) ∘ₗ co
  have hφ : ∀ b, φ b ∈ LinearMap.range co := by
    intro b
    rw [hcoC.2]
    exact hHCsp _ (by rw [← hcoC.2]; exact LinearMap.mem_range_self co b)
  let eco := LinearEquiv.ofInjective co hcoC.1
  let T : (Fin (D.n - 1) → ℂ) →ₗ[ℂ] Fin (D.n - 1) → ℂ :=
    eco.symm.toLinearMap ∘ₗ φ.codRestrict (LinearMap.range co) hφ
  have hT : ∀ b, co (T b) = H * co b * (H.map star)⁻¹ := by
    intro b
    have h2 := congrArg Subtype.val (eco.apply_symm_apply ⟨φ b, hφ b⟩)
    simpa [T, φ, eco, LinearEquiv.ofInjective_apply] using h2
  obtain ⟨Q, hQper, hQP, hQrel⟩ := hco.2.2.2
  have hfixL := hsees.1
  set lam := RootSumWeights.eigL G v B.β y a.2.1 with hlam
  have hlamspec : (LKCx.toV G v B.β y).val *ᵥ a.2.1 = lam • a.2.1 := by
    rw [hlam]
    simp only [RootSumWeights.eigL, dif_pos hfixL]
    exact hfixL.choose_spec
  have hne : a.2.1 ≠ 0 := by
    intro h0
    have := a.2.2
    rw [h0] at this
    simp at this
  have hinvmul : (LKCx.toV G v B.β y⁻¹).val * (LKCx.toV G v B.β y).val = 1 := by
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have hback : (LKCx.toV G v B.β y⁻¹).val *ᵥ (lam • a.2.1) = a.2.1 := by
    rw [← hlamspec, Matrix.mulVec_mulVec, hinvmul, Matrix.one_mulVec]
  have hlam0 : lam ≠ 0 := by
    intro h0
    apply hne
    rw [← hback, h0, zero_smul, Matrix.mulVec_zero]
  have hinvspec : (LKCx.toV G v B.β y⁻¹).val *ᵥ a.2.1 = lam⁻¹ • a.2.1 := by
    rw [Matrix.mulVec_smul] at hback
    rw [← hback, smul_smul, inv_mul_cancel₀ hlam0, one_smul]
    exact hback.symm ▸ rfl
  have hmark := RD.mark y⁻¹ Q a.2 H lam⁻¹ hQper hQrel (fun w => hHQ w Q hQP hQper) hinvspec
  rw [kap_inv] at hmark
  have hcy : ((↑(y⁻¹) : G.Cˣ × ℚˣ).1 : G.C) = (((↑y : G.Cˣ × ℚˣ).1)⁻¹ : G.Cˣ) := by
    simp [Subgroup.coe_inv, Prod.fst_inv]
  have hmin := hMinB p D G L B.β (U.Di i) j hco.1 ga ((↑(y⁻¹) : G.Cˣ × ℚˣ).1 : G.C) (fun u => hga u)
  rw [hcy] at hmin
  obtain ⟨hIv, hIdeg, hIsep⟩ := hInvMin G.F G.C ((↑y : G.Cˣ × ℚˣ).1)
  obtain ⟨hRdeg, hRsep⟩ := hRegSep p D G L v hv B a y hsees.1 (hreg _ hsees.2.1)
  have hdeg : (Polynomial.map (↑L.e.symm : G.F →+* D.F) (minpoly G.F (((↑y : G.Cˣ × ℚˣ).1)⁻¹ : G.Cˣ).val)).natDegree = D.n := by
    rw [Polynomial.natDegree_map, hIdeg, hRdeg, L.n_eq]
  have hsep : (Polynomial.map (↑L.e.symm : G.F →+* D.F) (minpoly G.F (((↑y : G.Cˣ × ℚˣ).1)⁻¹ : G.Cˣ).val)).Separable :=
    (hIsep hRsep).map
  obtain ⟨-, hEall⟩ := hEig D.F D.O D.inv D.g ρ (algebraMap (𝓞 D.F) D.O) D.n t₀ (epsD D) hsig (U.Di i) P Hm hper hHerm ga H hfix _ hmin hdeg hsep (D.n - 1) co hcoC T hT k α hα
  obtain ⟨-, hdetT, hdetF, hform⟩ := hEall _ hmark
  have hact : ∀ P' : (U.Di i).La →+ Fin D.g → ℂ, PELU.IsPeriod (U.Di i) ρ P' → ∀ (b : D.O) (z : Fin D.g → ℂ),
      Over.Hom.left (S.ex P' (ρ b *ᵥ z)) = Over.Hom.left (S.ex P' z) ≫ Over.Hom.left (X'.univ.act.act b) := by
    intro P' hP' b z
    rw [hSex, hSex, (U.unif i P' hP').2.2.2.2.1 b z, Over.comp_left]
    rfl
  have hEq : ∀ P₁ P₂ : (U.Di i).La →+ Fin D.g → ℂ, PELU.IsPeriod (U.Di i) ρ P₁ → PELU.IsPeriod (U.Di i) ρ P₂ →
      (∀ u, P₂ (ga u) = P₁ u) →
        S.u P₁ ≫ c₂.q = S.u P₂ ≫ c₁.q ∧
          ∀ z : Fin D.g → ℂ, Over.Hom.left (S.ex P₁ z) ≫ c₂.tot = Over.Hom.left (S.ex P₂ z) ≫ c₁.tot := by
    intro P₁ P₂ h1 h2 h12
    obtain ⟨hq, hz⟩ := hFixEq p D G L gb N N' h hlev X X' c₁ c₂ hX hL hX' hL' ρ hfine v t₀ B PD RD (U.Di i) (U.t i) (U.mem i) P j a hco y hsees ga hga P₁ P₂ (U.u i P₁) (U.u i P₂) (U.ex i P₁) (U.ex i P₂) (U.unif i P₁ h1) (U.unif i P₂ h2) h12
    refine ⟨by rw [hSu, hSu]; exact hq, fun z => by rw [hSex, hSex]; exact hz z⟩
  obtain ⟨hCorr, hInjP⟩ := hPow p D G L gb N N' h X X' c₁ c₂ ρ (U.Di i) S hact ga hEq k α
  obtain ⟨e₁, hUA1, he₁⟩ := hOneAt p D G L gb N N' h hlev X X' c₁ hX hL hX' hL' ρ hfine B PD (U.Di i) (U.t i) (U.mem i) j a.1 hco.1 hco.2.1 hco.2.2.1 P (U.u i P) (U.ex i P) hUA
  have hker : ∀ z z' : Fin D.g → ℂ, Over.Hom.left (S.ex P z) ≫ c₁.tot = Over.Hom.left (S.ex P z') ≫ c₁.tot → z - z' ∈ P.range := by
    intro z z' hzz
    rw [hSex, hSex] at hzz
    have hee : e₁ z = e₁ z' := Over.OverMorphism.ext (by rw [he₁ z, he₁ z']; exact hzz)
    have hsplit : e₁ z = e₁ z' * e₁ (z - z') := by rw [← hUA1.2.2.1.1, add_sub_cancel]
    rw [hee] at hsplit
    exact (hUA1.2.2.2.1 (z - z')).1 (mul_eq_left.mp hsplit.symm)
  have hinj := hInjP P hper hker
  have hrange : ∀ z : Fin k → Fin D.g → ℂ, (∀ s, z s ∈ P.range) →
      ∀ s, (fibMap H (diagAct (algebraMap (𝓞 D.F) D.O) ρ α)) z s ∈ P.range := by
    intro z hz s
    obtain ⟨x, hx⟩ := AddMonoidHom.mem_range.mp (hz s)
    refine AddMonoidHom.mem_range.mpr ⟨ga (algebraMap (𝓞 D.F) D.O (α s) • x), ?_⟩
    rw [hfix.2, hper.1, hx]
    simp [fibMap, diagAct, Matrix.toLin'_apply]
  obtain ⟨Fx, hFx, hAt⟩ := hLoc D.O D.inv D.g ρ (U.Di i) _ _ _ S (D.n - 1) hsm k _ (sZ X k) (c₁.pw k) (c₂.tw α) h₁ h₂ P Hm hper hHerm co hcoC ga H hfix T hT _ hCorr hrange hinj hdetT hdetF
  have hpc0 : perC P 0 = P := by
    ext x s
    simp [perC, PeriodCoord.realMap]
  have hpc1 : perC P (H * 0 * (H.map star)⁻¹) = P := by rw [mul_zero, zero_mul, hpc0]
  have hch := hChart _ _ _ ρ (U.Di i) _ _ _ S k _ (c₁.pw k) (c₂.tw α) P Hm hper hHerm ga H hfix _ hCorr 0
    (by rw [hpc0]; exact hper) (by rw [hpc1]; exact hper) 0
  rw [hpc0, hpc1, map_zero] at hch
  obtain ⟨hpt1, -, -, -, -⟩ := hPt _ _ _ ρ (U.Di i) _ _ _ S k P hper
  refine ⟨Fx, fun x => by have hx := hFx x; rw [hSu] at hx; exact hx, ⟨⟨S.pt k P 0, ?_⟩, (hFx _).2 ⟨hpt1 0, hch.symm⟩⟩, fun At hTan => ⟨(hAt At hTan).1, fun t => ?_⟩⟩
  · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ X'.s) (hpt1 0)).trans (S.ov P hper))
  · exact ((hAt At hTan).2 t).trans ((hform t).trans (by unfold wtFix; rw [hIv]))
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.heckeCoord_of :
    UpperTheory.Gal.W2.IsogAt → UpperTheory.Gal.W2.IsogCoord → UpperTheory.Gal.W2.HeckeCoord := by
  intro hA hC p _ D G L gb N N' h hlev X X' c hX hL hX' hL' ρ hF D' t P x e hU B j h₁ M hpl hco hloc
  obtain ⟨D'', t'', P'', e'', inc, d, hcls, hU'', hP, he, hd, hinc, f, nu, f'', nu'', hw, hw'', hf, hf'', hiff⟩ :=
    hA p D G L gb N N' h hlev X X' c hX hL hX' hL' ρ hF D' t P x e hU
  obtain ⟨h3, hNp, h3', hNp', -, hK⟩ := hlev
  obtain ⟨j'', hj, hpl'', hco'', hloc''⟩ :=
    hC p D G L B N N' (by omega) hNp (by omega) hNp' h hK ρ D' t D'' t'' P P'' inc d hU.2.1 hU''.2.1 hP hd hinc
      f nu f'' nu'' hw hw'' hf hf'' hiff j h₁ M hpl hco hloc
  refine ⟨D'', t'', P'', e'', inc, j'', hcls, hU'', hP, he, ?_, hj, hpl'', hco'', hloc''⟩
  intro u''
  obtain ⟨u, hu⟩ := hinc u''
  refine ⟨d, u, ?_, hu⟩
  rintro rfl
  have hp : p = 1 := by simpa using hd
  exact (Fact.out : p.Prime).one_lt.ne' hp
end
