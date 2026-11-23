module

public import Formalism.AdmissibleDesigns.TensSubsingleton
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Formalism.AdmissibleDesigns.InvariantsEqBotIff
public import Formalism.AdmissibleDesigns.TrCMemZ1D
public import Formalism.AdmissibleDesigns.Bundle001
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.Font

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N TensorProduct Formalism.MainNotions.N.K.TBa

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {O : Type} [CommRing O] [Algebra O LL]

theorem multV_zero_of_subsingleton {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V]
    [IsScalarTower Qp LL V] [Subsingleton V] (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) (a : ℤ) :
    multV PD ρ τ a = 0 := by
  have hs : ∀ b, Subsingleton ↥(FildR PD ρ τ b) := fun b =>
    ⟨fun x y => Subtype.ext ((tens_subsingleton (x : V ⊗[Qp] BdR)).trans (tens_subsingleton (y : V ⊗[Qp] BdR)).symm)⟩
  unfold multV
  haveI := hs a
  haveI := hs (a + 1)
  rw [Module.finrank_zero_of_subsingleton, Module.finrank_zero_of_subsingleton]
  rfl

variable {ι : Type} {k : ℕ} (Ms : ι → G →* Matrix (Fin k) (Fin k) LL)
  (hF : TruncatedSeriesCountingIdentities.FontaineAt PD LL O) (hMc : ∀ x, Continuous (Ms x))
include hF hMc

theorem mult_sum_neg : ∀ (m : ℕ) (xs : Fin m → ι), IsCrys PD (sumRep Ms xs) →
    (∀ (j : Fin m) (τ : K →ₐ[Qp] LL) (b : ℤ), IsJumpV PD (matRep (Ms (xs j))) τ b → 0 ≤ b) →
    ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), a < 0 → multV PD (sumRep Ms xs) τ a = 0 := by
  intro m
  induction m with
  | zero =>
    intro xs _ _ τ a _
    haveI : Subsingleton (Fin 0 → Fin k → LL) := inferInstance
    exact multV_zero_of_subsingleton PD _ τ a
  | succ m ih =>
    intro xs hc hJ τ a ha
    let A₀ : GRep G Qp LL O := sumG Ms hMc (fun a => xs a.succ)
    let A₁ : GRep G Qp LL O := sumG Ms hMc xs
    let A₂ : GRep G Qp LL O := matG Ms hMc (xs 0)
    let ι₀ : A₀.V →ₗ[LL] A₁.V := consZ (W := Fin k → LL) m
    let π₀ : A₁.V →ₗ[LL] A₂.V := LinearMap.proj (R := LL) (φ := fun _ : Fin (m + 1) => Fin k → LL) 0
    let σ₀ : A₂.V →ₗ[LL] A₁.V := consV (W := Fin k → LL) m
    have e1 : ∀ g x, ι₀ (A₀.ρ g x) = A₁.ρ g (ι₀ x) := fun g x => funext fun a => by
      cases a using Fin.cases
      · show (0 : Fin k → LL) = (Ms (xs 0) g).mulVec 0
        rw [Matrix.mulVec_zero]
      · rfl
    have e2 : ∀ g x, π₀ (A₁.ρ g x) = A₂.ρ g (π₀ x) := fun g x => rfl
    have hinj : Function.Injective ι₀ := consZ_inj (W := Fin k → LL) m
    have hsurj : Function.Surjective π₀ := fun v => ⟨σ₀ v, proj_consV (W := Fin k → LL) m v⟩
    have hex : LinearMap.range ι₀ = LinearMap.ker π₀ := range_consZ (W := Fin k → LL) m
    have hF1 := hF.1 A₀ A₁ A₂ ι₀ π₀ e1 e2 hinj hsurj hex
    obtain ⟨hc0, hc2, hadd⟩ := hF1.1 hc
    have h0 : multV PD A₀.ρ τ a = 0 :=
      ih (fun a => xs a.succ) hc0 (fun j => hJ j.succ) τ a ha
    have h2 : multV PD A₂.ρ τ a = 0 := by
      by_contra hne
      have := hJ 0 τ a (jump_of_mult PD _ τ a hne)
      omega
    show multV PD A₁.ρ τ a = 0
    rw [hadd τ a, h0, h2, add_zero]

theorem decomp_neg (A₁ A₀ : GRep G Qp LL O) {m : ℕ} (xs : Fin m → ι)
    (e : A₁.V ≃ₗ[LL] A₀.V × (Fin m → Fin k → LL))
    (he : ∀ g v, e (A₁.ρ g v) = (A₀.ρ g (e v).1, sumRep Ms xs g (e v).2))
    (hc : IsCrys PD A₁.ρ)
    (hJ : ∀ (j : Fin m) (τ : K →ₐ[Qp] LL) (b : ℤ), IsJumpV PD (matRep (Ms (xs j))) τ b → 0 ≤ b) :
    IsCrys PD A₀.ρ ∧ ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), a < 0 → multV PD A₁.ρ τ a = multV PD A₀.ρ τ a := by
  let A₂ : GRep G Qp LL O := sumG Ms hMc xs
  let ι₀ : A₀.V →ₗ[LL] A₁.V := e.symm.toLinearMap ∘ₗ LinearMap.inl LL A₀.V (Fin m → Fin k → LL)
  let π₀ : A₁.V →ₗ[LL] A₂.V := LinearMap.snd LL A₀.V (Fin m → Fin k → LL) ∘ₗ e.toLinearMap
  have e1 : ∀ g x, ι₀ (A₀.ρ g x) = A₁.ρ g (ι₀ x) := by
    intro g x
    apply e.injective
    show e (e.symm (A₀.ρ g x, 0)) = e (A₁.ρ g (e.symm (x, 0)))
    rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, map_zero]
  have e2 : ∀ g x, π₀ (A₁.ρ g x) = A₂.ρ g (π₀ x) := by
    intro g x
    show (e (A₁.ρ g x)).2 = sumRep Ms xs g (e x).2
    rw [he]
  have hinj : Function.Injective ι₀ := by
    intro x y h
    have h' : e.symm (x, 0) = e.symm (y, 0) := h
    have := congrArg Prod.fst (e.symm.injective h')
    exact this
  have hsurj : Function.Surjective π₀ := by
    intro y
    refine ⟨e.symm (0, y), ?_⟩
    show (e (e.symm (0, y))).2 = y
    rw [LinearEquiv.apply_symm_apply]
  have hex : LinearMap.range ι₀ = LinearMap.ker π₀ := by
    ext v
    constructor
    · rintro ⟨x, rfl⟩
      show (e (e.symm (x, 0))).2 = 0
      rw [LinearEquiv.apply_symm_apply]
    · intro hv
      have hv' : (e v).2 = 0 := hv
      refine ⟨(e v).1, ?_⟩
      show e.symm ((e v).1, 0) = v
      rw [← hv']
      exact e.symm_apply_apply v
  have hF1 := hF.1 A₀ A₁ A₂ ι₀ π₀ e1 e2 hinj hsurj hex
  obtain ⟨hc0, hc2, hadd⟩ := hF1.1 hc
  refine ⟨hc0, fun τ a ha => ?_⟩
  have h2 : multV PD A₂.ρ τ a = 0 := mult_sum_neg PD Ms hF hMc m xs hc2 hJ τ a ha
  rw [hadd τ a, h2, add_zero]

end Gen

section GenNT

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]

section DR

variable {V V' : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    {ρ : Representation LL G V} {ρ' : Representation LL G V'} (e : V ≃ₗ[LL] V')
    (he : ∀ g x, e (ρ g x) = ρ' g (e x))
include he

theorem isDR_congr (h : IsDR PD ρ) : IsDR PD ρ' := by
  let E : V ⊗[Qp] BdR ≃ₗ[LL] V' ⊗[Qp] BdR := AlgebraTensorModule.congr e (LinearEquiv.refl Qp BdR)
  have hE : ∀ g x, E (actVdR PD ρ g x) = actVdR PD ρ' g (E x) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [E, actVdR, he]
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb, map_add (f := _), map_add (f := _)]
  have hD : DdR PD ρ = (DdR PD ρ').comap (E : V ⊗[Qp] BdR →ₗ[LL] V' ⊗[Qp] BdR) := by
    ext x
    simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, Submodule.mem_comap, sub_eq_zero]
    constructor
    · intro hx g
      rw [LinearEquiv.coe_coe, ← hE, hx g]
    · intro hx g
      apply E.injective
      rw [hE]
      exact hx g
  unfold IsDR at h ⊢
  rw [← e.finrank_eq, ← h, hD]
  exact (E.ofSubmodule' (DdR PD ρ')).finrank_eq.symm

end DR

section MatT

variable {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] {k : ℕ}
  (M : G →* Matrix (Fin k) (Fin k) LL) (ρ' : Representation LL G V) (e : V ≃ₗ[LL] (Fin k → LL))
  (he : ∀ g x, e (ρ' g x) = matRep M g (e x))
include he

theorem crys_of_mat (h : IsCrys PD (matRep M)) : IsCrys PD ρ' := by
  refine Norm.isCrys_congr PD e.symm (fun g y => ?_) h
  apply e.injective
  rw [LinearEquiv.apply_symm_apply, he, LinearEquiv.apply_symm_apply]

theorem multV_mat (τ : K →ₐ[Qp] LL) (a : ℤ) : multV PD ρ' τ a = multV PD (matRep M) τ a :=
  Norm.multV_congr PD e he τ a

theorem dR_of_mat (h : IsDR PD (matRep M)) : IsDR PD ρ' := by
  refine isDR_congr PD e.symm (fun g y => ?_) h
  apply e.injective
  rw [LinearEquiv.apply_symm_apply, he, LinearEquiv.apply_symm_apply]

end MatT

end GenNT

end Formalism.MainNotions.N.K.Font

end
end

section

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.TB

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.WeaklyAdmissibleFiltrations Formalism.NG Formalism.RepresentationBoundsCohomology.BR

section Record

open Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i)
  (Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (Formalism.MainNotions.N.RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (Formalism.MainNotions.N.RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

abbrev Qcore (c : Fin (D.R.t + 1)) (n cB : ℕ) : Type :=
  ↥(Hc i dc Dd c n ⊓ divBy (Fc i dc Dd c n) (((D.nd.l i : ℕ) : D.nd.O i) ^ cB)) ⧸
    (Fc i dc Dd c n).comap (Hc i dc Dd c n ⊓ divBy (Fc i dc Dd c n) (((D.nd.l i : ℕ) : D.nd.O i) ^ cB)).subtype

def TBLenAt (cB : ℕ) (n : ℕ) (c : Fin (D.R.t + 1)) : Prop :=
  Module.length (D.nd.O i) (Qcore i dc Dd c n cB) ≤
    Module.length (D.nd.O i) (D.nd.O i ⧸ Ideal.span {((D.nd.l i : ℕ) : D.nd.O i)}) * (cB : ℕ∞) *
      ((Formalism.MainNotions.N.locDeg D.host.E (plOf i dc n) : ℕ∞) + 1)

def TBLen (cB : ℕ) : Prop :=
  ∀ n ∈ rowsN i dc, ∀ c : Fin (D.R.t + 1), 1 ≤ (c : ℕ) → TBLenAt i dc Dd cB n c

def TrivialBoundAtRows (cB : ℕ) : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), w ∈ dc.row →
    Formalism.MainNotions.N.TBAt (Br.PD D.loc D.nbr i w hw) (O := ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL)) (Br.inert D.nbr i w hw)
      (Jr i r π (TruncatedSeriesCountingIdentities.CoefExt.self i w hw)) D.R.t cB

theorem eW_symm_cont {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) :
    Continuous (eW i dc hw).symm := by
  have h1 : Continuous (D.nbr i w hw).e.symm := (D.nbr i w hw).e_symm_cont
  have h2 : Continuous (MulEquiv.subgroupCongr (Dw_idx i dc hw)).symm :=
    continuous_induced_rng.2 continuous_subtype_val
  exact h2.comp h1

theorem eW_inert {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (g : Dw i dc (idx i dc w)) (hg : g ∈ (Ine (F := D.host.E) (Aw i dc (idx i dc w))).subgroupOf (Dw i dc (idx i dc w))) :
    eW i dc hw g ∈ Br.inert D.nbr i w hw := by
  have hmem : w ∈ plSet i dc := by
    simp only [plSet, Finset.mem_union]
    exact Or.inl ((dc.cover w).2 hw)
  have hA : Aw i dc (idx i dc w) = D.nd.plOm.1 w := by
    unfold Aw
    rw [plOf_idx i dc hmem]
  unfold Br.inert
  rw [Subgroup.mem_subgroupOf, hA] at hg
  simp only [Subgroup.mem_comap, Subgroup.mem_subgroupOf, Br.iota]
  have hx : ((Br.ι (D.nbr i w hw) (eW i dc hw g)) : GE D.nd) = (g : GE D.nd) := by
    simp [Br.ι, eW]
  rw [hx]
  exact hg



theorem tbTarget_of (cB : ℕ) (hTB : TrivialBoundAtRows i dc r π cB) (hd : TBDict i dc r π Dd)
    (hlen : TBLen i dc Dd cB) : TBTarget i dc Dd cB := by
  intro n hn c hc
  have hlen' := hlen n hn c hc
  obtain ⟨w, hwrow, rfl⟩ := Finset.mem_image.1 hn
  have hw : w ∈ placesOver D.host.E (D.nd.l i) := (dc.cover w).1 (Or.inl hwrow)
  obtain ⟨Y, Cd, hY, hψ, hloc⟩ := hd w hw hwrow c hc
  have hT : Formalism.MainNotions.N.TBAt (Br.PD D.loc D.nbr i w hw) (O := ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL)) (Br.inert D.nbr i w hw)
      (Jr i r π (TruncatedSeriesCountingIdentities.CoefExt.self i w hw)) D.R.t cB := hTB w hw hwrow
  have het : (c : ℕ) - 1 < D.R.t := by
    have := c.2
    omega
  have hp : (Br.PD D.loc D.nbr i w hw).p = D.nd.l i := Br.PD_p D.loc D.nbr i w hw
  refine ⟨?_, le_rfl, ?_, hlen'⟩
  · unfold Fc Hc
    split_ifs
    · exact inf_le_left
    · exact bot_le
  · intro ψ hψe z hz
    unfold Fc
    split_ifs with h1
    · obtain ⟨hzl, m, hm⟩ := tb_zero (σ := selfO i hw) (M := Mc i Dd c) (eG := eW i dc hw) hT (by omega) het Y hY Cd hψ hloc (eW_symm_cont i dc hw) hp
        ((Ine (F := D.host.E) (Aw i dc (idx i dc w))).subgroupOf (Dw i dc (idx i dc w))) (eW_inert i dc hw)
        ψ hψe z hz
      rw [← map_smul]
      exact ⟨mem_locally_constant_of _ _ (hzl.comp (fun m => ((D.nd.l i : D.nd.O i) ^ cB) • m)),
        mem_unramified_of_coboundary _ _ _ m hm⟩
    · have := tb_pos (σ := selfO i hw) (M := Mc i Dd c) (eG := eW i dc hw) hT (by omega) het Y hY Cd hψ hloc (eW_symm_cont i dc hw) hp ψ hψe z hz
      rw [Submodule.mem_bot, ← map_smul]
      exact mkQ_eq_zero_of _ _ this

end Record

end Formalism.MainNotions.N.K.TB

end
end
