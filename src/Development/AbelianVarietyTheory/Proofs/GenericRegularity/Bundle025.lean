module

public import Development.AbelianVarietyTheory.Definitions.RegularCharts.Bundle001
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle014
public import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle013
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle024
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle023
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsFractionField
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle015
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle016
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle010
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle011
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle009
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle012
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.PublishedIntClosHolds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Definitions.RegularCharts.SCharts
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg.CellChart

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {M : MChart Y}

theorem lift_point_unique {R : Type} [CommRing R] [Algebra c.F R] {f : Γ(Y.X, M.U) →+* R} {x x' : Sp R ⟶ Xo.X}
    (Λ : M.Lift f x) (Λ' : M.Lift f x') : x = x' := by
  haveI := Y.jQ_open
  have h : Λ.xF = Λ'.xF := by
    rw [← cancel_mono Y.jQ]
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc]
      exact Λ.xF_j.trans Λ'.xF_j.symm
    · rw [Category.assoc, Category.assoc, Y.jQ_over]
      exact Λ.xF_snd.trans Λ'.xF_snd.symm
  rw [← Λ.xF_fst, h, Λ'.xF_fst]

theorem tie_unique {L : Type} [Field L] [Algebra c.F L] {f : Γ(Y.X, M.U) →+* L}
    {u : ∀ τ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult τ)) L} {y z : FrPt Xo c L} (hy : M.Comparison₂ f u y)
    (hz : M.Comparison₂ f u z) : y = z :=
  GlobalTheory.Reg.TieUniq.frPt_eq_of_tie E H Dw l Xo c O β Y M L f u y z hy hz (lift_point_unique hy.choose hz.choose)

theorem tie_congr {R : Type} [CommRing R] [Algebra c.F R] {f f' : Γ(Y.X, M.U) →+* R}
    {u u' : ∀ τ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult τ)) R} {y : FrPt Xo c R} (hy : M.Comparison₂ f u y)
    (hf : ∀ a, f a = f' a) (hu : ∀ τ i j, u τ i j = u' τ i j) : M.Comparison₂ f' u' y := by
  obtain rfl : f = f' := RingHom.ext hf
  obtain rfl : u = u' := funext fun τ => Matrix.ext (hu τ)
  exact hy

end

theorem mul_eq_smul_iff_cols {R : Type} [CommRing R] {n r : ℕ} (P : Matrix (Fin n) (Fin n) R) (N : R)
    (u : Matrix (Fin n) (Fin r) R) : P * u = N • u ↔ ∀ i, P.mulVec (fun j => u j i) = N • fun j => u j i :=
  ⟨fun h i => funext fun j => congrFun (congrFun h j) i, fun h => Matrix.ext fun j i => congrFun (h i) j⟩

end GlobalTheory.Reg.CellChart

namespace GlobalTheory.Reg


open GlobalTheory.Reg.CellChart in
theorem exists_pChart_of_cell : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), FrBC Xo c → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O c.F] [IsFractionRing O c.F] (Y : Model Xo c (algebraMap O c.F)), PushInvertible Y.t.G Y.t.PP.L → ∀ (M : MChart Y) (ix : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) ↪ Fin M.n), ∃ (J : Type) (_ : Finite J) (P : J → PChart Xo c (algebraMap O c.F)), ∀ (L : Type) [Field L] [Algebra c.F L] (W : ValuationSubring L) (f : Γ(Y.X, M.U) →+* L) (y : FrPt Xo c L) (Λ : M.Lift f y.x) (u : ∀ τ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult τ)) L) (b : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) L), (∀ a, f a ∈ W) → (∀ τ i j, u τ i j ∈ W) → (∀ τ, InCell (ix τ) (u τ)) → (∀ τ, (b τ).BlockTriangular id ∧ ∀ i, b τ i i ≠ 0) → Λ.LieTie (fun τ => u τ * b τ) y.u → ∃ j, (P j).Catches W y := by
  intro hS E _ _ _ H Dw l Xo c hbc O _ _ _ _ _ Y hpush M ix
  haveI := M.dom
  obtain ⟨α, es, -, hft, hinj, hne, hes, hop, hpt⟩ := GlobalTheory.Reg.ChartOpens.moduli_basicOpens E H Dw l Xo c O Y M
  obtain ⟨ρ, hρ⟩ := GlobalTheory.Reg.MChart.exists_ringHom_rho E H Dw l Xo c O _ Y M
  have hemb : Function.Injective (embF (E := E) c) := fun τ τ' h =>
    RingHom.ext fun a => congrArg Subtype.val (RingHom.congr_fun h a)
  choose N p hN hp using exists_projector E c.F (embF c) hemb O Γ(Y.X, M.U) α M.n ρ
  have heig : ∀ (R : Type) [CommRing R] [Algebra c.F R] (f : Γ(Y.X, M.U) →+* R),
      f.comp α = (algebraMap c.F R).comp (algebraMap O c.F) → ∀ τ x,
        M.Eig f τ x ↔ ((p τ).map f).mulVec x = f (α (N τ)) • x := by
    intro R _ _ f hf τ x
    rw [← (hp τ R f hf).2 x]
    simp only [hρ]
    rfl
  have hfN : ∀ (L : Type) [Field L] [Algebra c.F L] (f : Γ(Y.X, M.U) →+* L),
      f.comp α = (algebraMap c.F L).comp (algebraMap O c.F) → ∀ τ, f (α (N τ)) ≠ 0 := by
    intro L _ _ f hf τ
    rw [show f (α (N τ)) = algebraMap c.F L (algebraMap O c.F (N τ)) from RingHom.congr_fun hf _]
    exact (map_ne_zero _).mpr ((map_ne_zero_iff _ (IsFractionRing.injective O c.F)).mpr (hN τ))
  have hlift : ∀ e ∈ es, ∀ (R : Type) [CommRing R] [Algebra c.F R] (f : Γ(Y.X, M.U) →+* R),
      f.comp α = (algebraMap c.F R).comp (algebraMap O c.F) → IsUnit (f e) → ∃ x, Nonempty (M.Lift f x) := by
    intro e he R _ _ f hf hu
    obtain ⟨xF, h1, h2⟩ := (hop e he R f hf hu).1
    exact ⟨_, MChart.nonempty_lift E H Dw l Xo c O _ Y M R f xF h1 h2⟩
  have hrk : ∀ (L : Type) [Field L] [Algebra c.F L] (f : Γ(Y.X, M.U) →+* L),
      f.comp α = (algebraMap c.F L).comp (algebraMap O c.F) →
      ∀ e ∈ es, f e ≠ 0 → ∀ τ, ((p τ).map f).rank = Dw.mult τ := by
    intro L _ _ f hf e he hfe τ
    obtain ⟨x, ⟨Λ⟩⟩ := hlift e he L f hf hfe.isUnit
    let S : Submodule L (Fin M.n → L) := Module.End.eigenspace ((p τ).map f).mulVecLin (f (α (N τ)))
    have hS' : ∀ y, y ∈ S ↔ ((p τ).map f).mulVec y = f (α (N τ)) • y := fun y => Module.End.mem_eigenspace_iff
    rw [rank_of_quasi_idem _ _ (hfN L f hf τ) (hp τ L f hf).1 S hS']
    exact GlobalTheory.Reg.finrank_chart_eig E H Dw l Xo c O _ Y M L f x Λ τ S fun y => (hS' y).trans (heig L f hf τ y).symm
  have hpoint : ∀ (L : Type) [Field L] [Algebra c.F L] (f : Γ(Y.X, M.U) →+* L) (y : FrPt Xo c L)
      (Λ : M.Lift f y.x) (u : ∀ τ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult τ)) L)
      (b : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) L),
      (∀ τ, (b τ).BlockTriangular id ∧ ∀ i, b τ i i ≠ 0) → Λ.LieTie (fun τ => u τ * b τ) y.u →
      f.comp α = (algebraMap c.F L).comp (algebraMap O c.F) ∧ (∃ e ∈ es, f e ≠ 0) ∧
        ∀ τ, (p τ).map f * u τ = f (α (N τ)) • u τ := by
    intro L _ _ f y Λ u b hb ht
    obtain ⟨hf, he⟩ := hpt L f Λ.xF Λ.xF_snd Λ.xF_j
    refine ⟨hf, he, fun τ => ?_⟩
    have h1 : (p τ).map f * (u τ * b τ) = f (α (N τ)) • (u τ * b τ) :=
      (mul_eq_smul_iff_cols _ _ _).mpr fun i => (heig L f hf τ _).mp
        ((GlobalTheory.Reg.isEigAt_iff_eig E H Dw l Xo c O _ Y M L f y.x Λ τ _ _ (ht τ i)).mp (y.eig τ i))
    have hd : IsUnit (b τ).det := by
      rw [Matrix.det_of_upperTriangular (hb τ).1]
      exact (Finset.prod_ne_zero_iff.mpr fun i _ => (hb τ).2 i).isUnit
    have h2 := congrArg (· * (b τ)⁻¹) h1
    simp only [Matrix.mul_assoc, Matrix.smul_mul, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one] at h2
    exact h2
  by_cases hκ : ∃ κ₀ : ∀ τ, Fin (Dw.mult τ) → Fin M.n, ∀ τ, ((p τ).submatrix (ix τ) (κ₀ τ)).det ≠ 0
  swap
  · refine ⟨Empty, inferInstance, Empty.elim, fun L _ _ W f y Λ u b _ _ hc hb ht => (hκ ?_).elim⟩
    obtain ⟨hf, -, hu⟩ := hpoint L f y Λ u b hb ht
    choose κ hκL using fun τ => exists_minor _ _ (hfN L f hf τ) (ix τ) (u τ) (hu τ) (hc τ)
    refine ⟨κ, fun τ h => hκL τ ?_⟩
    have := RingHom.map_det f ((p τ).submatrix (ix τ) (κ τ))
    rw [h, map_zero] at this
    exact this.symm
  obtain ⟨κ₀, hκ₀⟩ := hκ
  obtain ⟨Ω, _, _, gens, es', g, u, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
    exists_cell_algebra c.F O Γ(Y.X, M.U) (E →+* ℂ) α hft hinj es hes hne M.n Dw.mult ix N hN p
      (fun L _ _ f hf τ => (hp τ L f hf).1) hrk (fun e he R _ _ f hf hu => (hop e he R f hf hu).2) κ₀ hκ₀
  choose hsm fe ue k1 k2 k3 k4 k5 k6 using h8
  have hy : ∀ e (he : e ∈ es'), ∃ y : FrPt Xo c (Algebra.adjoin c.F (insert e⁻¹ (gens : Set Ω))),
      M.Comparison₂ (fe e he) (ue e he) y := by
    intro e he
    obtain ⟨e₀, he₀, hu⟩ := k4 e he
    obtain ⟨x, ⟨Λ⟩⟩ := hlift e₀ he₀ _ (fe e he) (k3 e he) hu
    obtain ⟨y, -, hy⟩ := GlobalTheory.Reg.exists_frPt_tie hS E H Dw l Xo c O _ Y M _ (fe e he) x Λ (ue e he)
      (fun τ i => (heig _ _ (k3 e he) τ _).mpr ((mul_eq_smul_iff_cols _ _ _).mp (k5 e he τ) i))
      (fun τ cv h => k6 e he τ cv ((heig _ _ (k3 e he) τ _).mp h))
    exact ⟨y, hy⟩
  choose yy hyy using hy
  have hgen : ∀ e (he : e ∈ es') z, FrMap (Algebra.adjoin c.F (insert e⁻¹ (gens : Set Ω))).val (yy e he) z →
      M.Comparison₂ g u z := fun e he z hz =>
    tie_congr (GlobalTheory.Reg.MChart.tie_baseChange E H Dw l Xo c O _ Y M _ _ _ _ _ _ _ (hyy e he) hz) (k1 e he) (k2 e he)
  obtain ⟨e₁, he₁⟩ := id h2
  obtain ⟨yg, hyg⟩ := hbc _ _ (Algebra.adjoin c.F (insert e₁⁻¹ (gens : Set Ω))).val (yy e₁ he₁)
  have hint : ∀ e (he : e ∈ es') (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra
      ∀ (ψ : Algebra.adjoin c.F (insert e⁻¹ (gens : Set Ω)) →ₐ[c.F] T.Fr),
        (∀ a : O, io (algebraMap O c.F a) ∈ Set.range (algebraMap T.V T.Fr)) →
        (∀ w : Algebra.adjoin c.F (insert e⁻¹ (gens : Set Ω)), (w : Ω) ∈ gens →
          ψ w ∈ Set.range (algebraMap T.V T.Fr)) →
        ∀ z : FrPt Xo c T.Fr, FrMap ψ (yy e he) z → Integral T io z := by
    intro e he T io
    letI := io.toAlgebra
    intro ψ hO hg z hz
    have hVinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective _ _
    have hB : ∀ w ∈ Subring.closure (Set.range ((algebraMap c.F Ω).comp (algebraMap O c.F)) ∪ (gens : Set Ω)),
        w ∈ (((algebraMap T.V T.Fr).range.comap ψ.toRingHom).map
          (Algebra.adjoin c.F (insert e⁻¹ (gens : Set Ω))).val.toRingHom) := by
      intro w hw
      refine (Subring.closure_le.mpr ?_) hw
      rintro w (⟨o, rfl⟩ | hw)
      · refine ⟨algebraMap c.F _ (algebraMap O c.F o), ?_, rfl⟩
        obtain ⟨v, hv⟩ := hO o
        exact ⟨v, hv.trans (ψ.commutes _).symm⟩
      · exact ⟨⟨w, Algebra.subset_adjoin (Or.inr hw)⟩, hg _ hw, rfl⟩
    have hfa : ∀ a, ψ.toRingHom.comp (fe e he) a ∈ (algebraMap T.V T.Fr).range := by
      intro a
      obtain ⟨w, hw, hw'⟩ := hB _ (h4 a)
      obtain rfl : w = fe e he a := Subtype.ext (hw'.trans (k1 e he a).symm)
      exact hw
    let φ := (algebraMap T.V T.Fr).rangeRestrict
    let ε : T.V ≃+* (algebraMap T.V T.Fr).range := RingEquiv.ofBijective φ
      ⟨fun a b h => hVinj (congrArg Subtype.val h), (algebraMap T.V T.Fr).rangeRestrict_surjective⟩
    let f₀ : Γ(Y.X, M.U) →+* T.V := ε.symm.toRingHom.comp ((ψ.toRingHom.comp (fe e he)).codRestrict _ hfa)
    have hf₀ : ∀ a, algebraMap T.V T.Fr (f₀ a) = ψ (fe e he a) := fun a =>
      congrArg Subtype.val (ε.apply_symm_apply ⟨_, hfa a⟩)
    choose u₀ hu₀ using fun τ i j => hg (ue e he τ i j) (by rw [k2]; exact h5 τ i j)
    refine GlobalTheory.Reg.tie_integral hS E H Dw l Xo c O _ Y M hpush T io f₀ ix u₀ (fun τ => ⟨fun i j hij => hVinj ?_,
      fun i => hVinj ?_⟩) z (tie_congr (GlobalTheory.Reg.MChart.tie_baseChange E H Dw l Xo c O _ Y M _ _ _ _ _ _ _ (hyy e he) hz)
        (fun a => (hf₀ a).symm) fun τ i j => (hu₀ τ i j).symm)
    · rw [hu₀, show ue e he τ (ix τ i) j = 0 from Subtype.ext ((k2 e he τ _ _).trans ((h7 τ).1 i j hij)),
        map_zero, map_zero]
    · rw [hu₀, show ue e he τ (ix τ i) i = 1 from Subtype.ext ((k2 e he τ _ _).trans ((h7 τ).2 i)),
        map_one, map_one]
  let P : PChart Xo c (algebraMap O c.F) :=
    { Ω := Ω, gens := gens, frac := h1, es := es', es_ne := h2, es_mem := h3, sm := hsm, yg := yg, y := yy
      gen := fun e he => by
        obtain ⟨z, hz⟩ := hbc _ _ (Algebra.adjoin c.F (insert e⁻¹ (gens : Set Ω))).val (yy e he)
        rw [tie_unique (hgen _ _ _ hyg) (hgen _ _ _ hz)]
        exact hz
      int := hint }
  refine ⟨Unit, inferInstance, fun _ => P, fun L _ _ W f y Λ u' b hW hW' hc hb ht => ⟨(), ?_⟩⟩
  obtain ⟨hf, ⟨e₀, he₀, hfe⟩, hu⟩ := hpoint L f y Λ u' b hb ht
  obtain ⟨e, he, ψ, hψ1, hψ2⟩ := h9 L f hf e₀ he₀ hfe u' hu hc
  obtain ⟨z, hz⟩ := hbc _ _ ψ (yy e he)
  have htz : M.Comparison₂ f u' z := by
    refine tie_congr (GlobalTheory.Reg.MChart.tie_baseChange E H Dw l Xo c O _ Y M _ _ _ _ _ _ _ (hyy e he) hz) (fun a => ?_) fun τ i j => ?_
    · exact (congrArg ψ (Subtype.ext (k1 e he a))).trans (hψ1 a (k1 e he a ▸ (fe e he a).2))
    · exact (congrArg ψ (Subtype.ext (k2 e he τ i j))).trans (hψ2 τ i j (k2 e he τ i j ▸ (ue e he τ i j).2))
  obtain ⟨t, ht'⟩ := GlobalTheory.Reg.frBor_of_tie E H Dw l Xo c O _ Y M L f y z Λ u' b (lift_point_unique htz.choose Λ) hb ht htz
  refine ⟨e, he, ψ, z, t, ?_, hz, ht'⟩
  rintro ⟨w, hw⟩ hwg
  rcases h6 w hwg with ⟨a, rfl⟩ | ⟨τ, i, j, rfl⟩
  · exact (hψ1 a hw).symm ▸ hW a
  · exact (hψ2 τ i j hw).symm ▸ hW' τ i j

end GlobalTheory.Reg
end

section

noncomputable section

namespace GlobalTheory.Reg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem tie_integral_of_any_model : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (T : CDVR) (io : c.F →+* T.Fr) (f₀ : Γ(Y.X, M.U) →+* T.V) (ix : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) ↪ Fin M.n) (u₀ : ∀ τ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult τ)) T.V), (∀ τ, InCell (ix τ) (u₀ τ)) → letI := io.toAlgebra; ∀ z : FrPt Xo c T.Fr, M.Comparison₂ ((algebraMap T.V T.Fr).comp f₀) (fun τ => (u₀ τ).map (algebraMap T.V T.Fr)) z → Integral T io z := by
  intro hS E _ _ _ H Dw l Xo c O _ β Y M T io f₀ ix u₀ hu
  letI := io.toAlgebra
  intro z ⟨Λ, hL, hT⟩
  obtain ⟨PP, cub, sym, adj, prim, m, hm⟩ :=
    sabPull Out.CubePf.cubePull (spMap f₀ ≫ M.hU.fromSpec) Y.t
  have e : spMap ((algebraMap T.V T.Fr).comp f₀) ≫ M.hU.fromSpec =
      spMap (algebraMap T.V T.Fr) ≫ spMap f₀ ≫ M.hU.fromSpec := by
    rw [← Category.assoc]
    congr 1
    simp only [spMap, ← Spec.map_comp]
    rfl
  have key : ∀ (g : Sp T.Fr ⟶ Y.X) (n : SABMap Λ.t' Y.t g),
      g = spMap (algebraMap T.V T.Fr) ≫ spMap f₀ ≫ M.hU.fromSpec →
      ∃ m2 : SABMap Λ.t' _ (spMap (algebraMap T.V T.Fr)), m2.φ ≫ m.φ = n.φ := by
    intro g n hg
    subst hg
    obtain ⟨m2, h⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m n
    exact ⟨m2, h.symm⟩
  obtain ⟨m2, h2⟩ := key _ Λ.m2 e
  exact ⟨_, Λ.t', Λ.m1, m2,
    tie_vectors_integral E H Dw l Xo c O β Y M T io f₀ ix u₀ hu z Λ hL _ m m2 h2,
    GlobalTheory.T.exists_integralGenerator_chartPoint_noInvert hS E H Dw l Xo c O β Y M T io f₀ z.x z.s Λ hT _ m m2 h2⟩

end GlobalTheory.Reg
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem _root_.GlobalTheory.T.isCuspForm_of_integral_over_dominantWeight : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), AllTest Xo c → ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n N : ℕ) (w : Fin N → Rul Xo c), Dom a n → (∀ i, w i ∈ Formalism.L2.PjFree.cusp Xo c U a n) → ∀ (k m : ℕ) (cf : ℕ → MvPolynomial (Fin N) c.F), 0 < k → (∀ i < m, (cf i).IsHomogeneous ((m - i) * k)) → ∀ g ∈ sec Xo c (k • a) (k * n), g * g ^ m + ∑ i ∈ Finset.range m, (g * MvPolynomial.aeval w (cf i)) * g ^ i = 0 → g ∈ Formalism.L2.PjFree.cusp Xo c U (k • a) (k * n) := by
  first | exact @GlobalTheory.cusp_of_integral_of_dom | exact GlobalTheory.cusp_of_integral_of_dom | (intros; apply GlobalTheory.cusp_of_integral_of_dom <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif GlobalTheory.FrameNorm
open scoped Matrix nonZeroDivisors

theorem _root_.GlobalTheory.T.triangular_frame_change_of_triangular_period : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (k : Fin F.n) (P P₀ : (F.Di k).La →+ (Fin g → ℂ)) (h₀ : Matrix (Fin g) (Fin g) ℂ) (y y₀ : FrPt Xo c (CAt σ)), IsPeriod (F.Di k) (fun j => relab c σ (e j).1) P → IsPeriod (F.Di k) (fun j => relab c σ (e j).1) P₀ → (∀ a, P₀ a = h₀ *ᵥ P a) → (∀ j j', h₀ j j' ≠ 0 → (e j).1 = (e j').1 ∧ ((e j).2 : ℕ) ≤ (e j').2) → y.x = F.u k P → y₀.x = F.u k P₀ → (∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex k P z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) (y.u τ i)) → (∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex k P₀ z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) (y₀.u τ i)) → ∃ t : Ix Dw → (CAt σ)ˣ, FrBor t y₀ y ∧ ∀ j, toC (t (some (e j)) : CAt σ) = h₀ j j := by
  first | exact @GlobalTheory.FrameNorm.frBor_of_triangular_period | exact GlobalTheory.FrameNorm.frBor_of_triangular_period | (intros; apply GlobalTheory.FrameNorm.frBor_of_triangular_period <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj

namespace GlobalTheory.GaussVal

section
variable {O L U Γ : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L]
  [IsFractionRing O L] [Field U] [LinearOrderedCommGroupWithZero Γ] (v : Valuation U Γ)


omit [Field L] [Algebra O L] [IsFractionRing O L] in
theorem val_lt_one (g : O →+* U) (h1 : ∀ a, v (g a) ≤ 1) {ϖ : O} (hϖ : Irreducible ϖ) (h2 : v (g ϖ) < 1)
    {a : O} (ha : a ∈ IsLocalRing.maximalIdeal O) : v (g a) < 1 := by
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at ha
  obtain ⟨y, rfl⟩ := ha
  rw [map_mul, map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_right' (h1 y)) h2

theorem isInteger_of_val_le (φ : L →+* U) (h1 : ∀ a, v (φ (algebraMap O L a)) ≤ 1) {ϖ : O} (hϖ : Irreducible ϖ)
    (h2 : v (φ (algebraMap O L ϖ)) < 1) {c : L} (hc : v (φ c) ≤ 1) : ∃ a, algebraMap O L a = c := by
  rcases ValuationRing.isInteger_or_isInteger O c with h | ⟨b, hb⟩
  · exact h
  by_cases hc0 : c = 0
  · exact ⟨0, by simp [hc0]⟩
  by_cases hu : IsUnit b
  · obtain ⟨u, rfl⟩ := hu
    refine ⟨((u⁻¹ : Oˣ) : O), ?_⟩
    rw [map_units_inv, hb, inv_inv]
  · exfalso
    have := val_lt_one v (φ.comp (algebraMap O L)) h1 hϖ h2 (a := b) hu
    rw [RingHom.comp_apply, hb] at this
    have h3 : v (φ c) * v (φ c⁻¹) = 1 := by rw [← map_mul, ← map_mul, mul_inv_cancel₀ hc0, map_one, map_one]
    exact absurd h3 (lt_of_le_of_lt (mul_le_of_le_one_left' hc) this).ne
end

theorem val_unit {A U Γ : Type} [CommRing A] [Field U] [LinearOrderedCommGroupWithZero Γ] (v : Valuation U Γ)
    (g : A →+* U) (h1 : ∀ a, v (g a) ≤ 1) {a : A} (ha : IsUnit a) : v (g a) = 1 := by
  obtain ⟨b, hb⟩ := ha.exists_right_inv
  refine le_antisymm (h1 a) ?_
  have h3 : v (g a) * v (g b) = 1 := by rw [← map_mul, ← map_mul, hb, map_one, map_one]
  exact h3.symm.le.trans (mul_le_of_le_one_right' (h1 b))

theorem exists_approx {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K))
    (c t : la.adicCompletion K) (ht : t ≠ 0) :
    ∃ (a : K) (y : la.adicCompletionIntegers K), c - algebraMap K _ a = t * (y : la.adicCompletion K) := by
  have ho : IsOpen {x : la.adicCompletion K | t⁻¹ * (c - x) ∈ la.adicCompletionIntegers K} :=
    (Valued.isOpen_valuationSubring (la.adicCompletion K)).preimage (f := fun x => t⁻¹ * (c - x)) (by fun_prop)
  obtain ⟨a, ha⟩ := (HeightOneSpectrum.denseRange_algebraMap K la).exists_mem_open ho ⟨c, by simp⟩
  exact ⟨a, ⟨_, ha⟩, by rw [mul_inv_cancel_left₀ ht]⟩

noncomputable section

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}
  (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ)

local instance : IsDomain (Op X la N) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors (Op X la N) (gI X la N).primeCompl_le_nonZeroDivisors

local instance : Field (Kp X la N) :=
  inferInstanceAs (Field (FractionRing (Op X la N)))

local instance : Algebra (Op X la N) (Kp X la N) :=
  (inferInstance : Algebra (Op X la N) (FractionRing (Op X la N)))

local instance : IsFractionRing (Op X la N) (Kp X la N) :=
  (inferInstance : IsFractionRing (Op X la N) (FractionRing (Op X la N)))

local instance : Algebra (X.Ol la) (Kp X la N) :=
  ((algebraMap (Op X la N) (Kp X la N)).comp (algebraMap (X.Ol la) (Op X la N))).toAlgebra

private theorem gaussIntegerMap_injective :
    Function.Injective (algebraMap (X.Ol la) (Kp X la N)) :=
  (IsFractionRing.injective (Op X la N) (Kp X la N)).comp (Op.algebraMap_injective X la N)

local instance : Algebra (X.Kl la) (Kp X la N) :=
  (IsFractionRing.lift (K := X.Kl la) (g := algebraMap (X.Ol la) (Kp X la N))
    (by exact gaussIntegerMap_injective X la N)).toAlgebra

local instance : IsScalarTower (X.Ol la) (X.Kl la) (Kp X la N) :=
  IsScalarTower.of_algebraMap_eq fun c =>
    (IsFractionRing.lift_algebraMap (K := X.Kl la) (gaussIntegerMap_injective X la N) c).symm

local instance : IsScalarTower (X.Ol la) (Op X la N) (Kp X la N) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem gauss_dense_gen : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) (U : Type) [Field U] (v : Valuation U (WithZero (Multiplicative ℤ))) (ψ : Kp X la N →+* U), (∀ a : Op X la N, v (ψ (algebraMap (Op X la N) (Kp X la N) a)) ≤ 1) → v (ψ (algebraMap (Op X la N) (Kp X la N) (unifO X la N))) < 1 → (∀ (f : B.KO →+* U), (∀ a, f a = ψ (algebraMap (X.Kl la) (Kp X la N) (algebraMap B.KO (X.Kl la) a))) → ∀ p : MvPolynomial (Idx D j N) B.KO, (∀ α, v (f (p.coeff α)) ≤ 1) → (∃ α, v (f (p.coeff α)) = 1) → v (MvPolynomial.eval₂ f (fun q => ψ (algebraMap (Op X la N) (Kp X la N) (Tv X la N q))) p) = 1) ∧ (∀ (c : X.Ol la) (γ : WithZero (Multiplicative ℤ)), γ ≠ 0 → ∃ a : B.KO, v (ψ (algebraMap (X.Ol la) (Kp X la N) c) - ψ (algebraMap (X.Kl la) (Kp X la N) (algebraMap B.KO (X.Kl la) a))) < γ) ∧ ∀ S : Subfield U, (∀ c : X.Ol la, ψ (algebraMap (X.Ol la) (Kp X la N) c) ∈ S) → (∀ q, ψ (algebraMap (Op X la N) (Kp X la N) (Tv X la N q)) ∈ S) → ∀ c : Kp X la N, ψ c ∈ S := by
  intro D B P j X la N U _ v ψ h1 h2
  have hϖ : Irreducible (unif X la) :=
    Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible (X.Ol la))
  have e1 : ∀ c : X.Ol la, algebraMap (X.Kl la) (Kp X la N) (algebraMap (X.Ol la) (X.Kl la) c) =
      algebraMap (Op X la N) (Kp X la N) (algebraMap (X.Ol la) (Op X la N) c) := fun c => by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have eC : ∀ c : X.Ol la, algebraMap (Pol X la N) (Op X la N) (MvPolynomial.C c) =
      algebraMap (X.Ol la) (Op X la N) c := fun c => by
    rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
  set φ : X.Kl la →+* U := ψ.comp (algebraMap (X.Kl la) (Kp X la N)) with hφ
  have g1 : ∀ a, v (φ (algebraMap (X.Ol la) (X.Kl la) a)) ≤ 1 := fun a => by
    rw [hφ, RingHom.comp_apply, e1]; exact h1 _
  have g2 : v (φ (algebraMap (X.Ol la) (X.Kl la) (unif X la))) < 1 := by
    rw [hφ, RingHom.comp_apply, e1]; exact h2
  refine ⟨?_, ?_, ?_⟩
  · intro f hf p hp ⟨α₀, hα₀⟩
    have hf' : ∀ a, f a = φ (algebraMap B.KO (X.Kl la) a) := hf
    have hex : ∀ α, ∃ a : X.Ol la, algebraMap (X.Ol la) (X.Kl la) a = algebraMap B.KO (X.Kl la) (p.coeff α) :=
      fun α => isInteger_of_val_le v φ g1 hϖ g2 (by rw [← hf']; exact hp α)
    choose b hb using hex
    set p₀ : Pol X la N := ∑ α ∈ p.support, MvPolynomial.monomial α (b α) with hp₀
    have hs : α₀ ∈ p.support := by
      rw [MvPolynomial.mem_support_iff]
      intro h
      rw [h, map_zero, map_zero] at hα₀
      exact zero_ne_one hα₀
    have hc : p₀.coeff α₀ = b α₀ := by
      classical
      rw [hp₀, MvPolynomial.coeff_sum]
      simp only [MvPolynomial.coeff_monomial]
      rw [Finset.sum_ite_eq', ite_eq_left hs]
    have hn : p₀ ∉ gI X la N := by
      unfold gI Formalism.DV.gaussIdeal
      rw [MvPolynomial.mem_map_C_iff]
      intro h
      have := val_lt_one v (φ.comp (algebraMap (X.Ol la) (X.Kl la))) g1 hϖ g2 (h α₀)
      rw [hc, RingHom.comp_apply, hb, ← hf', hα₀] at this
      exact lt_irrefl _ this
    have hu : IsUnit (algebraMap (Pol X la N) (Op X la N) p₀) :=
      (IsLocalization.AtPrime.isUnit_to_map_iff (Op X la N) (gI X la N) p₀).2 hn
    have := val_unit v (ψ.comp (algebraMap (Op X la N) (Kp X la N))) h1 hu
    rw [← this]
    congr 1

    rw [MvPolynomial.eval₂_eq, hp₀, map_sum, map_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [MvPolynomial.monomial_eq, map_mul, map_mul, eC, hf', ← hb, hφ, RingHom.comp_apply, e1, Finsupp.prod,
      map_prod, map_prod]
    simp only [map_pow]
    rfl
  · intro c γ hγ
    obtain ⟨n, hn⟩ := exists_pow_lt₀ g2 (Units.mk0 γ hγ)
    have ht : algebraMap (X.Ol la) (X.Kl la) (unif X la) ^ n ≠ 0 := by
      refine pow_ne_zero _ ?_
      rw [Ne, IsFractionRing.to_map_eq_zero_iff]
      exact hϖ.ne_zero
    obtain ⟨a, y, hy⟩ := exists_approx la (algebraMap (X.Ol la) (X.Kl la) c) _ ht
    refine ⟨a, ?_⟩
    rw [IsScalarTower.algebraMap_apply (X.Ol la) (X.Kl la) (Kp X la N)]
    change v (φ _ - φ _) < γ
    rw [← map_sub, hy, map_mul, map_mul, map_pow, map_pow]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (g1 y)) hn
  · intro S hO hT
    have hP : ∀ q : Pol X la N,
        ψ (algebraMap (Op X la N) (Kp X la N) (algebraMap (Pol X la N) (Op X la N) q)) ∈ S := by
      intro q
      induction q using MvPolynomial.induction_on with
      | C a => rw [eC]; exact hO a
      | add p q hp hq => simp only [map_add (f := _)]; exact S.add_mem hp hq
      | mul_X p i hp => simp only [map_mul]; exact S.mul_mem hp (hT i)
    have hA : ∀ x : Op X la N, ψ (algebraMap (Op X la N) (Kp X la N) x) ∈ S := by
      intro x
      obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj (gI X la N).primeCompl x
      have hs : ψ (algebraMap (Op X la N) (Kp X la N) (algebraMap (Pol X la N) (Op X la N) s)) ≠ 0 :=
        (((IsLocalization.map_units (Op X la N) s).map _).map _).ne_zero
      have h' := congrArg (fun z => ψ (algebraMap (Op X la N) (Kp X la N) z)) h
      simp only [map_mul] at h'
      rw [eq_div_of_mul_eq hs h']
      exact S.div_mem (hP _) (hP _)
    intro c
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := Op X la N) c
    rw [map_div₀]
    exact S.div_mem (hA _) (hA _)

end

end GlobalTheory.GaussVal
end
