module

public import Formalism.LocalToGlobal.IndefiniteReal.Bridge
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AtTauExUniqueHolds
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle008
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle015
import Formalism.LocalToGlobal.Divisibility.RowLatLemmas
public import Formalism.LocalToGlobal.GlobalTheory.DivPassageP
public import Formalism.LocalToGlobal.GlobalTheory.Bundle003
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle016
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle011
public import Formalism.LocalToGlobal.IndefiniteReal.RowGSurj
import Formalism.LocalToGlobal.IndefiniteReal.Bundle003
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.AuxStatement14
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.SecondStepGluing
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle018
public import Formalism.LocalToGlobal.Columns.Bundle004
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.TopMult

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Adelic

variable {D : D7} {V : HSp D}

theorem mem_GfC' (h : GA D V) : h ∈ GfC V ↔ (Eqv.matA D V h).map (infPart D) = 1 := by
  show (infHom V) h = 1 ↔ _
  rw [Units.ext_iff]
  exact Iff.rfl

theorem psiT_of_mem_GfC' {h : GA D V} (hh : h ∈ GfC V) (τ : D.what₂.Tau) : (Eqv.matA D V h).map (Eqv.psiT D τ) = 1 := by
  have h1 := (mem_GfC' h).1 hh
  unfold Eqv.psiT
  rw [RingHom.coe_comp, ← Matrix.map_map, h1]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem inf_GinfC_GfC' : GinfC V ⊓ GfC V = ⊥ := by
  rw [eq_bot_iff]
  rintro a ⟨ha, hb⟩
  rw [Subgroup.mem_bot]
  apply Eqv.matA_inj D V
  rw [Eqv.matA_one]
  apply Eqv.mat_ext D
  · intro τ
    rw [psiT_of_mem_GfC' hb τ, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [(Eqv.mem_GinfC D V a).1 ha, Matrix.map_one _ (map_zero _) (map_one _)]

theorem mem_GfC_of_psiT {h : GA D V} (hh : ∀ τ, (Eqv.matA D V h).map (Eqv.psiT D τ) = 1) : h ∈ GfC V := by
  rw [mem_GfC']
  ext i j
  rw [Matrix.map_apply]
  apply (Eqv.splitEquiv D).injective
  funext τ
  have e := congrFun (congrFun (hh τ) i) j
  rw [Matrix.map_apply] at e
  rw [Eqv.splitEquiv_apply, Eqv.splitEquiv_apply]
  change Eqv.psiT D τ (Eqv.matA D V h i j) = _
  rw [e]
  by_cases hij : i = j
  · subst hij; simp
  · simp [Matrix.one_apply_ne hij]

theorem ga_decomp (g : GA D V) : ∃ h ∈ GfC V, ∃ a ∈ GinfC V, g = h * a := by
  refine ⟨g * (Eqv.infOnly D V g)⁻¹, mem_GfC_of_psiT fun τ => ?_, Eqv.infOnly D V g, Eqv.infOnly_mem_GinfC D V g,
    (inv_mul_cancel_right g _).symm⟩
  have h1 : (Eqv.matA D V g).map (Eqv.psiT D τ) = (Eqv.matA D V (Eqv.infOnly D V g)).map (Eqv.psiT D τ) := by
    rw [← Eqv.infMat_thetaC, ← Eqv.infMat_thetaC, Eqv.infMat_infOnly]
  rw [Eqv.matA_mul, Matrix.map_mul, h1, ← Matrix.map_mul, ← Eqv.matA_mul, mul_inv_cancel, Eqv.matA_one,
    Matrix.map_one _ (map_zero _) (map_one _)]

theorem ginf_mem_closure {θ : Datum.InfFam D} (hθ : IsInfFam θ) {a : GA D V} (ha : a ∈ GinfC V) :
    a ∈ Submonoid.closure {x | ∃ τ, ∃ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), x = atTau θ V τ g} := by
  obtain rfl := Eqv.eq_thetaC D hθ
  classical
  set gs : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ := fun τ => infMat D.sp.cm.sig V.gram (Eqv.thetaC D τ) a
  have hgs : Eqv.IsUnitFam D V gs := Eqv.infMat_unitary' D V a
  have hu : ∀ s : Finset D.what₂.Tau, Eqv.IsUnitFam D V (fun τ => if τ ∈ s then gs τ else 1) := by
    intro s τ
    by_cases hτ : τ ∈ s
    · simp only [hτ, if_true]; exact hgs τ
    · simp only [hτ, if_false]; simp
  have key : ∀ s : Finset D.what₂.Tau, Eqv.famH D V _ (hu s) ∈
      Submonoid.closure {x | ∃ τ, ∃ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), x = atTau (Eqv.thetaC D) V τ g} := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have e : Eqv.famH D V _ (hu ∅) = 1 := by
        apply Eqv.matA_inj D V
        rw [Eqv.matA_famH, Eqv.matA_one]
        convert Eqv.famM_one D V using 2
        funext τ
        simp
      rw [e]
      exact Submonoid.one_mem _
    | insert τ0 s hτ0 ih =>
      have e : Eqv.famH D V _ (hu (insert τ0 s)) = Eqv.atH D V τ0 (gs τ0) (hgs τ0) * Eqv.famH D V _ (hu s) := by
        apply Eqv.matA_inj D V
        rw [Eqv.matA_famH, Eqv.matA_mul, Eqv.matA_atH, Eqv.matA_famH]
        apply Eqv.mat_ext D
        · intro τ
          rw [Matrix.map_mul, Eqv.psi_famM, Eqv.psi_atM, Eqv.psi_famM]
          by_cases h : τ = τ0
          · subst h; simp [hτ0]
          · simp [h]
        · rw [Matrix.map_mul, Eqv.fin_famM, Eqv.fin_atM, Eqv.fin_famM, Matrix.one_mul]
      rw [e]
      refine Submonoid.mul_mem _ (Submonoid.subset_closure ⟨τ0, gs τ0, hgs τ0, ?_⟩) ih
      exact (Eqv.atTau_eq D V τ0 (gs τ0) (hgs τ0)).symm
  have e : a = Eqv.famH D V _ (hu Finset.univ) :=
    Eqv.famH_unique D V _ (hu Finset.univ) a ha (fun τ => by simp [gs])
  rw [e]
  exact key Finset.univ

end Adelic

section GenAd

variable {G Γ : Type} [Group G] [Group Γ] {ι : Γ →* G} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ} {F : G → W}

end GenAd

section GenHom

variable {G H : Type} [Group G] [Group H] (f : G →* H)

end GenHom

section Generic

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : Datum.InfFam D) (M : DSModel V S) (c : CoefA V)
  (pr : c.W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ)

theorem rr_of_GinfC {a : GA D V} (ha : a ∈ GinfC V) : (finHom V).rangeRestrict a = 1 := Subtype.ext (MonoidHom.mem_ker.mp ha)

theorem atTau_mem_GinfC (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) : atTau θ V τ g ∈ GinfC V := by
  unfold atTau
  split_ifs with h
  · exact h.choose_spec.1
  · exact Subgroup.one_mem _

variable {θ M c pr}

variable {J' : Subgroup (Bridge.Gf V)} {χ' : J' →* ℂˣ} {F : Bridge.Gf V → c.W}






theorem exists_lift (y : Bridge.Gf V) : ∃ h, h ∈ GfC V ∧ (finHom V).rangeRestrict h = y := by
  obtain ⟨g, rfl⟩ := (finHom V).rangeRestrict_surjective y
  obtain ⟨h, hh, a, ha, rfl⟩ := ga_decomp g
  exact ⟨h, hh, by rw [map_mul, rr_of_GinfC ha, mul_one]⟩

theorem lift_unique {h h' : GA D V} (hh : h ∈ GfC V) (hh' : h' ∈ GfC V)
    (e : (finHom V).rangeRestrict h = (finHom V).rangeRestrict h') : h = h' := by
  have h1 : h⁻¹ * h' ∈ GinfC V := by
    show h⁻¹ * h' ∈ (finHom V).ker
    have e2 := congrArg Subtype.val e
    simp only [MonoidHom.coe_rangeRestrict] at e2
    rw [MonoidHom.mem_ker, map_mul, map_inv, e2, inv_mul_cancel]
  have h2 : h⁻¹ * h' ∈ GfC V := mul_mem (inv_mem hh) hh'
  have h3 : h⁻¹ * h' ∈ GinfC V ⊓ GfC V := ⟨h1, h2⟩
  rw [inf_GinfC_GfC', Subgroup.mem_bot] at h3
  exact inv_mul_eq_one.mp h3



end Generic

section Real

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]


end Real

end Formalism.IndefR.TopMult
end
end

section

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.CxPass

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.L2.GlobalTheoryTheory.DivPassage

namespace In3

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
  (I : In3 K G Pl0 I0 Ty T m)

def rep (h1 : I.ρf 1 = 1) (hm : ∀ g h, I.ρf (g * h) = I.ρf g * I.ρf h) : Representation K G (Fin I.Sg.D → K) where
  toFun g := Matrix.toLin' (I.ρf g)
  map_one' := by rw [h1, Matrix.toLin'_one]; rfl
  map_mul' g h := by rw [hm, Matrix.toLin'_mul]; rfl

theorem rep_apply (h1 : I.ρf 1 = 1) (hm : ∀ g h, I.ρf (g * h) = I.ρf g * I.ρf h) (g : G) (x : Fin I.Sg.D → K) :
    I.rep h1 hm g x = I.ρf g *ᵥ x := by
  first
  | rfl
  | simp [rep, Matrix.toLin'_apply]

theorem epM_eq (h1 : I.ρf 1 = 1) (hm : ∀ g h, I.ρf (g * h) = I.ρf g * I.ρf h) (P : Subgroup G) (ψ : P →* Kˣ)
    (χ : P →* (𝓞 K)ˣ) (hχ : ∀ h, (((χ h : (𝓞 K)ˣ) : 𝓞 K) : K) = ((ψ h : Kˣ) : K)) :
    (I.epM P ψ).mulVecLin = Formalism.IndefR.TransferLatticeStatement.epP P χ (I.rep h1 hm) := by
  rw [← Matrix.toLin'_apply']

  simp only [epM, Formalism.IndefR.TransferLatticeStatement.epP, map_smul, map_sum, hχ, map_inv]
  congr 1
  refine Finset.sum_congr (by congr; exact Subsingleton.elim _ _) (fun h _ => ?_)
  have e := hχ h⁻¹
  rw [map_inv χ, map_inv ψ] at e
  rw [e]
  rfl

theorem eMat_eq (h1 : I.ρf 1 = 1) (hm : ∀ g h, I.ρf (g * h) = I.ρf g * I.ρf h) {W : Type} [AddCommGroup W]
    [Module K W] (τ : Representation K G W) :
    (I.eMat τ).mulVecLin = Formalism.IndefR.TransferLatticeStatement.eS τ (I.rep h1 hm) := by
  rw [← Matrix.toLin'_apply']

  simp only [eMat, Formalism.IndefR.TransferLatticeStatement.eS, map_smul, map_sum]
  rfl

theorem passage_of_steps [_root_.NumberField.IsTotallyComplex K] {s : ℕ} (H : I.Hyp s) {S : Type} [Fintype S] {Ws : S → Type}
    [∀ s, AddCommGroup (Ws s)] [∀ s, Module K (Ws s)] [∀ s, FiniteDimensional K (Ws s)]
    (τ : ∀ s, Representation K G (Ws s)) (nbar : ℝ) (N : IndefNum I.A3.fam3.base3)
    (hρ : I.PRho) (hJ : I.PJ) (hR : I.PRange) (hMet : I.PMet) (hFr : I.PFrames) (hU : I.PUni)
    (hLat : I.PLat) (hGL : I.PGLat) (hS : I.PSand) (hGood : I.PGood τ)
    (hτ : Formalism.IndefR.TransferLatticeStatement.IsGood τ) (hX : CharsX τ I.A.fam.X) (hM1 : Formalism.IndefR.IndefiniteEpsilonOperator.M1 τ ⟨I.P0, I.ψ0⟩) (hn : 0 < nbar)
    (hM2 : NearConstantMultiplicities τ ⟨I.P1, I.ψ1⟩ nbar N.de) (hla : N.la = Formalism.IndefR.IndefiniteEpsilonOperator.la G) :
    Passage N (I.Sb false) (I.Sb true) := by
  obtain ⟨h1, hm, -⟩ := hρ s H
  obtain ⟨χ0, hχ0⟩ := Formalism.IndefR.LatticeTransfer.liftChar K I.P0 I.ψ0
  obtain ⟨χ1, hχ1⟩ := Formalism.IndefR.LatticeTransfer.liftChar K I.P1 I.ψ1
  have hFrm : (I.LA τ nbar).FramesG := hFr s H
  have hL : (I.LA τ nbar).LatG := by
    classical
    letI : Finite T := H.ok.ok2.tup_fin
    letI : Fintype T := Fintype.ofFinite T
    let L : T → Submodule (𝓞 K) (Fin I.Sg.D → K) := fun t => matLat (I.X.rowMat I.cg false t)
      ((lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).abelian₂ t)
    have hfull : ∀ t, Submodule.IsFullLattice K (L t) := fun t =>
      matLat_full _ (rowG_surj H t) _
        (BlockDat.Lam_full H.ok.ok2.conj (H.ok.ok2.what₂ t) H.ok.ok2.irr)
    choose a ha0 ha using fun t => GluingInclusion.denom (K := K) (L I.A3.fam3.base3.μ0) (L t)
      (Submodule.IsLattice.fg (self := (hfull _).toIsLattice)) (hfull t).span_eq_top
    let d := ∏ t, a t
    have hd : d ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun t _ => ha0 t)
    have hle : ∀ x ∈ L I.A3.fam3.base3.μ0, x ∈ Submodule.span K (I.Sg.RR : Set _) := by
      intro x hx
      have hdx : d • x ∈ I.Sg.RR := by
        apply (I.mem_RRg).2
        intro w
        obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem a (Finset.mem_univ (I.X.μ w))
        have hdmem : d • x ∈ L (I.X.μ w) := by
          change (∏ t, a t) • x ∈ L (I.X.μ w)
          rw [hr, mul_comm, mul_smul]
          exact (L _).smul_mem r (ha _ x hx)
        obtain ⟨z, hz, hz'⟩ := (exponent_index_lattice.mem_matLat _ _ _).mp hdmem
        refine ⟨1, one_mem _, z, hz, ?_⟩
        rw [one_smul]
        exact hz'
      have hdK : algebraMap (𝓞 K) K d ≠ 0 := (IsFractionRing.injective (𝓞 K) K).ne hd
      have hmem : d • x ∈ Submodule.span K (I.Sg.RR : Set (Fin I.Sg.D → K)) :=
        Submodule.subset_span hdx
      have hs := (Submodule.span K (I.Sg.RR : Set (Fin I.Sg.D → K))).smul_mem
        (algebraMap (𝓞 K) K d)⁻¹ hmem
      rw [← algebraMap_smul K d x, smul_smul, inv_mul_cancel₀ hdK, one_smul] at hs
      exact hs
    refine { toIsLattice := hLat s H, span_eq_top := ?_ }
    exact top_unique (by rw [← (hfull I.A3.fam3.base3.μ0).span_eq_top]; exact Submodule.span_le.mpr hle)
  have key0 : (I.LA τ nbar).ep0.mulVecLin = Formalism.IndefR.TransferLatticeStatement.epP I.P0 χ0 (I.rep h1 hm) :=
    I.epM_eq h1 hm I.P0 I.ψ0 χ0 hχ0
  have key1 : (I.LA τ nbar).ep1.mulVecLin = Formalism.IndefR.TransferLatticeStatement.epP I.P1 χ1 (I.rep h1 hm) :=
    I.epM_eq h1 hm I.P1 I.ψ1 χ1 hχ1
  have hs : ∀ t : S, (I.eMat (τ t)).mulVecLin = Formalism.IndefR.TransferLatticeStatement.eS (τ t) (I.rep h1 hm) := fun t =>
    I.eMat_eq h1 hm (τ t)
  have hnS : ∀ t : S, Formalism.IndefR.IndefiniteEpsilonOperator.nOf (τ t) ⟨I.P1, I.ψ1⟩ = Formalism.IndefR.TransferLatticeStatement.nS (τ t) I.P1 χ1 := fun t =>
    nOf_eq_nS (τ t) I.P1 I.ψ1 χ1 hχ1
  have hM1' : Formalism.IndefR.TransferLatticeStatement.M1 τ I.P0 χ0 := fun t => by rw [← nOf_eq_nS (τ t) I.P0 I.ψ0 χ0 hχ0]; exact hM1 t
  have hgood : Formalism.IndefR.TransferLatticeStatement.eGood τ (I.rep h1 hm) = LinearMap.id := by
    unfold Formalism.IndefR.TransferLatticeStatement.eGood
    rw [← Finset.sum_congr rfl fun t _ => hs t]
    apply LinearMap.ext
    intro x
    have hx := congrArg (fun M : Matrix (Fin I.Sg.D) (Fin I.Sg.D) K => M *ᵥ x) (hGood s H hτ hX)
    simp only [Matrix.sum_mulVec, Matrix.one_mulVec] at hx
    rw [LinearMap.sum_apply, LinearMap.id_apply]
    simpa only [Matrix.mulVecLin_apply] using hx
  have hst : ∀ g : G, ∀ a ∈ I.Sg.RR, I.rep h1 hm g a ∈ I.Sg.RR := fun g a ha => by
    rw [rep_apply]; exact hGL s H g a ha
  have hUn : Formalism.IndefR.TransferLatticeStatement.IsUnitaryRep (Pi.basisFun K (Fin I.Sg.D)) I.Sg.XE (I.rep h1 hm) := fun v g x y => by
    rw [rep_apply, rep_apply]; exact hU s H v g x y
  obtain ⟨hRk, hD0, hD1, hMx⟩ := Formalism.IndefR.LatticeTransfer.levelAmb_transfer (I.LA τ nbar) τ I.P0 χ0 I.P1 χ1 (I.rep h1 hm) hτ hM1'
    key0 key1 hs hnS rfl hgood hFrm hL hst hUn
  have hE : ∀ b, (I.LA τ nbar).EmbAt (I.Jm b) (I.epM (I.lvP b) (I.lvψ b)) (Nat.card (I.lvP b)) (I.Sb b).XE := fun b =>
    ⟨(hJ s H b).2, hR s H b, hMet s H b⟩
  have hSd : ∀ b, (I.LA τ nbar).SandAt (I.Jm b) (I.epM (I.lvP b) (I.lvψ b)) (Nat.card (I.lvP b)) (I.Sb b).RR := by
    intro b
    obtain ⟨hin, hout⟩ := hS s H b
    refine ⟨?_, ?_⟩
    · rintro y ⟨x, hx, rfl⟩
      refine ⟨hin x hx, ?_⟩
      show (I.Jm b *ᵥ x) ∈ LinearMap.range (I.epM (I.lvP b) (I.lvψ b)).mulVecLin
      rw [← hR s H b]; exact ⟨x, rfl⟩
    · rintro y ⟨hyR, hyE⟩
      obtain ⟨x, hx, hxy⟩ := hout y hyR hyE
      exact ⟨x, hx, hxy⟩
  have hRows : (I.LA τ nbar).RowsG :=
    ⟨Formalism.L2.GlobalTheoryTheory.DivPassage2.rows_gen (I.LA τ nbar) hL (I.Jm false) _ H.pos0 (hJ s H false).2 (hR s H false),
      Formalism.L2.GlobalTheoryTheory.DivPassage2.rows_gen (I.LA τ nbar) hL (I.Jm true) _ H.pos1 (hJ s H true).2 (hR s H true)⟩
  have hSz : (I.LA τ nbar).Sizes N.la := by
    refine ⟨Nat.card_pos, ?_, Nat.card_pos, ?_, ?_⟩
    · exact (Subgroup.card_le_card_group I.P0).trans (Nat.card_eq_fintype_card).le
    · exact (Subgroup.card_le_card_group I.P1).trans (Nat.card_eq_fintype_card).le
    · rw [hla]; exact le_refl _
  exact passage_from_levels K I.A3.fam3.base3 _ _ N (I.Sb false) (I.Sb true) (I.LA τ nbar) hFrm hL (hE false) (hE true)
    (hSd false) (hSd true) hSz hRk hD0 hD1 (hMx hRows.2) ⟨hn, hM2⟩ hRows

end In3

def Steps3 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G] [Fintype G] (Pl0 I0 Ty T : Type) (m : ℕ)
    (I : In3 K G Pl0 I0 Ty T m), I.PRho ∧ I.PJ ∧ I.PRange ∧ I.PMet ∧ I.PFrames ∧ I.PUni ∧ I.PLat ∧ I.PGLat ∧ I.PSand ∧
      ∀ (S : Type) [Fintype S] (Ws : S → Type) [∀ s, AddCommGroup (Ws s)] [∀ s, Module K (Ws s)]
        [∀ s, FiniteDimensional K (Ws s)] (τ : ∀ s, Representation K G (Ws s)), I.PGood τ

theorem cutPassage3S_of_steps (h : Steps3) : CutPassage3S := by
  intro K _ _ _ _ G _ _ Pl0 I0 Ty T m A3 s P0 ψ0 P1 ψ1 Dc Sp Zsc X C CH gE S _ Ws _ _ _ τ nbar
    hok hsep hst hin h4 hp0 hp1 hh2 hrat hh2g hratg hgu hge hn0 hn1 hτ hX hM1 hn hM2 hla
  let I : In3 K G Pl0 I0 Ty T m := ⟨A3, P0, ψ0, P1, ψ1, Dc, Sp, Zsc, X, gE⟩
  obtain ⟨hρ, hJ, hR, hMet, hFr, hU, hLat, hGL, hS, hG⟩ := h K G Pl0 I0 Ty T m I
  exact I.passage_of_steps ⟨hok, hsep, hst, hin, h4, hp0, hp1, hh2, hrat, hh2g, hratg, hgu, hge, hn0, hn1⟩
    τ nbar _ hρ hJ hR hMet hFr hU hLat hGL hS (hG S Ws τ) hτ hX hM1 hn hM2 hla

end Formalism.IndefR.CxPass
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S IsDedekindDomain NumberField
open scoped TensorProduct

namespace Formalism.IndefR.principalLevelFrame

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def tensCastR {E : Type} [Field E] [NumberField E] {F1 F2 : Subfield E} (h : F1 = F2) :
    FiniteAdeleRing (𝓞 F1) F1 ⊗[F1] E ≃+* E ⊗[F2] FiniteAdeleRing (𝓞 F2) F2 := by
  subst h
  exact (Algebra.TensorProduct.comm F1 (FiniteAdeleRing (𝓞 F1) F1) E).toRingEquiv

variable {D : D7}

def StdPsi {V : HSp D} {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (P : RowPsi V n) : Prop :=
  (∃ (β : Matrix (Fin V.rank) (Fin n) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E))
      (β' : Matrix (Fin n) (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)),
      β * β' = 1 ∧ β' * β = 1 ∧
      ∀ κ, finMat D.sp.cm.sig V.gram (P.ψ κ) =
        β * ((κ.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL D.host.E)).map (tensCastR hF).symm) * β') ∧
  ∀ κ, κ ∈ ReciprocityTheory.Aut.Umax D.host.E n ↔ P.ψ κ ∈ KsphC V ∅

def RowRepTie {V : HSp D} {n : ℕ} {Sp : D.what₂.Tau → SPar} (rowRep : D.what₂.FT → Formalism.L2.NG.FinTyp D.host.E n)
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (PY : RowPsi V n) (M : Formalism.IndefR.Mult.DSModel V Sp) (J : Bool → Set (GA D V))
    (χ : Bool → GA D V → ℂ) (e : Bool → (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (eFT : D.what₂.FT ≃ FTR θ PY M J χ e) : Prop :=
  ∀ σ, (rowRep σ).Iso (rowRepR θ (eFT σ))

def RowLocPin {V : HSp D} {Sp : D.what₂.Tau → SPar} (lp : Formalism.L2.LPTiedPlaceholder D)
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (PY : RowPsi V D.R.r)
    (M : Formalism.IndefR.Mult.DSModel V Sp) (J : Bool → Set (GA D V)) (χ : Bool → GA D V → ℂ)
    (e : Bool → (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (eFT : D.what₂.FT ≃ FTR θ PY M J χ e) : Prop :=
  Formalism.L2.RowLocTied D lp (Formalism.L2.Col.rowFrameOf D (OccRows θ PY M J χ e) eFT)

end Formalism.IndefR.principalLevelFrame

end
end
