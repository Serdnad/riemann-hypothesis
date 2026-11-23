module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle450
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle385
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachDeltaInvariantsReductionIsLattice
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle013
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle164
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle422
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle409
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle449
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.EmbedsLevelZeroDepthZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle453
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle163
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle014
public import Formalism.LocalRingCardinality.Bundle004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle416
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NlenLeLenN
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle312
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle451
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle452
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
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
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Formalism.ConjugateSelfDual.Bundle001
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLqPerm

theorem isChar_one {G : Type} [Group G] : IsChar (fun _ : G => (1 : ℂ)) := by
  refine ⟨FDRep.of (Representation.trivial ℂ G ℂ), fun x => ?_⟩
  change LinearMap.trace ℂ ℂ ((Representation.trivial ℂ G ℂ) x) = 1
  simp [Representation.trivial, LinearMap.trace_id]

theorem isClass_of_isChar {G : Type} [Group G] {χ : G → ℂ} (h : IsChar χ) : IsClass χ := by
  obtain ⟨V, hV⟩ := h
  intro x y
  rw [← hV, ← hV, FDRep.char_conj]

variable {g : ℕ} [Fact g.Prime]

theorem isChar_hcL (L : List (Pc g)) (hL : ∀ p ∈ L, IsChar p.2) : IsChar (hcL L (degL L)) := by
  induction L with
  | nil => exact isChar_one
  | cons p L ih =>
    have hdeg : degL (p :: L) = p.1 + degL L := by simp [degL]
    rw [hcL_cons]
    exact ((GlobalTheory.T.harishChandra_induction_character_restriction_decomp g p.1 (degL L) (degL (p :: L)) hdeg).1 p.2 (hcL L (degL L))
      (hL p (by simp)) (ih fun q hq => hL q (by simp [hq])))

theorem degL_perm {L L' : List (Pc g)} (h : L.Perm L') : degL L = degL L' := by
  unfold degL
  exact (h.map _).sum_eq

theorem hc_congr_mid (a : ℕ) (α : Gn g a → ℂ) (F : (m : ℕ) → Gn g m → ℂ) (n m m' : ℕ) (h : m = m') :
    hc a m α (F m) n = hc a m' α (F m') n := by subst h; rfl

theorem hc_congr_left (c : ℕ) (γ : Gn g c → ℂ) (F : (m : ℕ) → Gn g m → ℂ) (n m m' : ℕ) (h : m = m') :
    hc m c (F m) γ n = hc m' c (F m') γ n := by subst h; rfl

theorem hcL_perm {L L' : List (Pc g)} (h : L.Perm L') :
    (∀ p ∈ L, IsChar p.2) → ∀ n, n = degL L → hcL L n = hcL L' n := by
  induction h with
  | nil => intro _ n _; rfl
  | cons x h ih =>
    rename_i L₁ L₂
    intro hc1 n hn
    rw [hcL_cons, hcL_cons, ih (fun q hq => hc1 q (by simp [hq])) _ rfl]
    exact hc_congr_mid x.1 x.2 (hcL L₂) n _ _ (degL_perm h)
  | swap x y L₁ =>
    intro hc1 n hn
    have hx : IsClass x.2 := isClass_of_isChar (hc1 x (by simp))
    have hy : IsClass y.2 := isClass_of_isChar (hc1 y (by simp))
    have hL : IsClass (hcL L₁ (degL L₁)) :=
      isClass_of_isChar (isChar_hcL L₁ fun q hq => hc1 q (by simp [hq]))
    have hn' : n = y.1 + x.1 + degL L₁ := by rw [hn]; simp [degL]; omega
    have hn'' : n = x.1 + y.1 + degL L₁ := by rw [hn']; omega
    have e1 : degL (x :: L₁) = x.1 + degL L₁ := by simp [degL]
    have e2 : degL (y :: L₁) = y.1 + degL L₁ := by simp [degL]
    simp only [hcL_cons]
    rw [hc_congr_mid y.1 y.2 (fun m => hc x.1 (degL L₁) x.2 (hcL L₁ (degL L₁)) m) n _ _ e1,
      hc_congr_mid x.1 x.2 (fun m => hc y.1 (degL L₁) y.2 (hcL L₁ (degL L₁)) m) n _ _ e2]
    rw [← (GlobalTheory.T.harishChandraInductionExteriorProduct_assoc_comm g y.1 x.1 (degL L₁) n y.2 x.2 _ hy hx hL).1 hn',
      ← (GlobalTheory.T.harishChandraInductionExteriorProduct_assoc_comm g x.1 y.1 (degL L₁) n x.2 y.2 _ hx hy hL).1 hn'',
      (GlobalTheory.T.harishChandraInductionExteriorProduct_assoc_comm g y.1 x.1 (degL L₁) (y.1 + x.1) y.2 x.2 _ hy hx hL).2.1 rfl]
    exact hc_congr_left (degL L₁) (hcL L₁ (degL L₁)) (fun m => hc x.1 y.1 x.2 y.2 m) n _ _ (Nat.add_comm _ _)
  | trans h₁ h₂ ih₁ ih₂ =>
    intro hc1 n hn
    rw [ih₁ hc1 n hn, ih₂ (fun q hq => hc1 q (h₁.mem_iff.mpr hq)) n (hn.trans (degL_perm h₁))]

end GlobalTheory.GLqPerm

theorem GlobalTheory.gl_list_product_perm_char : ∀ (g : ℕ) [Fact g.Prime] (L L' : List (Pc g)) (n : ℕ), n = degL L → (∀ p ∈ L, IsChar p.2) → IsChar (hcL L n) ∧ (L.Perm L' → hcL L n = hcL L' n) := by
  intro g _ L L' n hn hL
  subst hn
  exact ⟨GlobalTheory.GLqPerm.isChar_hcL L hL, fun h => GlobalTheory.GLqPerm.hcL_perm h hL _ rfl⟩
end

section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.wachDeltaInvariants_reduction_isLattice : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (S : TopSit P) (k : Type) [Field k] [Algebra S.O k] [CharP k l], S.IsRes k → ∀ {R : RingPG k l} (ι : k⸨X⸩ →ₐ[k] k⸨X⸩) (F : DFun R S.n S.G) (τ : ZMod S.n → ZMod (Module.finrank ℚ_[l] ↥(K0 S.K))) (γ : (S.W H).Gam) (p : Pres (S.W H) F ι τ γ), GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι → (∀ i, (S.W H).emb (τ i) = S.emb i) → ((S.W H).χΓ γ : S.O) = 1 + (l : S.O) → GlobalTheory.WachUse.QN (S.W H) → ∀ (T : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) (A : Ob k S.G) q (U : ZMod S.n → Multiset ℤ), Onto T A q → KerIs S.Γ.lam q → CrysWith (P.PD S.K) S.emb T.ρ U → ∃ N : Lats k S.n A.m, (∀ i y, y ∈ N i ↔ ∃ x : ↥(DΔ (S.W H) T), (x : (S.W H).DD T) ∈ (S.W H).N T ∧ p.j T A q i x = y) ∧ ∀ i, IsLat (N i) := by
  first | exact @GlobalTheory.Present.RedLat.red_isLat | exact GlobalTheory.Present.RedLat.red_isLat | (intros; apply GlobalTheory.Present.RedLat.red_isLat <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.LTChar

theorem char_cont : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (x : P.R.B), P.ιB x ∈ Fil P 1 → P.ιB x ∉ Fil P 2 → ∀ (c : ↥(GK K) → ↥(MaximalUnramifiedExtension l)), (∀ g : ↥(GK K), P.actQ (g : GQ l) x = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (c g) * x) → Continuous fun g => ((c g : ↥(MaximalUnramifiedExtension l)) : Om l) := by
  intro l _ P AI T K x h1 h2 c hc
  obtain ⟨-, -, hsh, -, -, -, -, hact, -⟩ := GlobalTheory.PMon.bdR_tied l P AI T
  obtain ⟨S, θ, hS, -, hker, hOm, hθ⟩ := GlobalTheory.PMon.exists_theta_deRhamFilZero_surjective_alt l P AI T
  have hu0 : tz P (-1) * P.ιB x ∈ Fil P 0 := by
    have := (hsh 1 (-1) _).1 h1
    simpa using this
  have hu1 : tz P (-1) * P.ιB x ∉ Fil P 1 := by
    intro h
    apply h2
    rw [hsh 2 (-1)]
    simpa using h
  set u : S := ⟨tz P (-1) * P.ιB x, (hS _).2 hu0⟩ with hu
  have hy : θ u ≠ 0 := fun h => hu1 ((hker u).1 h)
  have key : ∀ g : ↥(GK K), (((c g : ↥(MaximalUnramifiedExtension l)) : Om l) : ℂ_[l]) =
      algebraMap ℚ_[l] ℂ_[l] ((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) * Formalism.Per.σC (g : GQ l) (θ u) / θ u := by
    intro g
    obtain ⟨hg, hg'⟩ := hθ g u
    obtain ⟨ha, ha'⟩ := hOm (algebraMap ℚ_[l] (Om l) ((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]))
    obtain ⟨hb, hb'⟩ := hOm ((c g : ↥(MaximalUnramifiedExtension l)) : Om l)
    have e : (⟨_, ha⟩ : S) * ⟨_, hg⟩ = ⟨_, hb⟩ * u := by
      apply Subtype.ext
      show algebraMap (Om l) P.R.BdR _ * P.actQdR g (tz P (-1) * P.ιB x) = kd P (c g) * (tz P (-1) * P.ιB x)
      rw [map_mul, hact, ← iota_act, hc, map_mul, iota_kur, ← IsScalarTower.algebraMap_apply, ← mul_assoc, ← mul_assoc, ← mul_assoc,
        ← map_mul, ← Units.val_mul]
      simp only [zpow_neg, zpow_one, mul_inv_cancel, Units.val_one, map_one]
      ring
    have e' := congrArg θ e
    rw [map_mul θ, map_mul θ, ha', hb', hg'] at e'
    rw [eq_div_iff hy, ← e']
    rfl
  have hemb : Topology.IsEmbedding (fun y : Om l => (y : ℂ_[l])) :=
    UniformSpace.Completion.coe_isometry.isEmbedding
  refine hemb.continuous_iff.2 ?_
  have : ((fun y : Om l => (y : ℂ_[l])) ∘ fun g => ((c g : ↥(MaximalUnramifiedExtension l)) : Om l)) = _ := funext key
  rw [this]
  refine Continuous.div_const (Continuous.mul ?_ ?_) _
  · exact (continuous_algebraMap ℚ_[l] ℂ_[l]).comp
      ((GlobalTheory.Cyc.IsCyc.continuous P.χQ_cyc).comp continuous_subtype_val)
  · exact (orbit_cont (θ u)).comp continuous_subtype_val

end GlobalTheory.LTChar
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.lubinTate_period_conj_ratio_unramified : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (s : ℕ), 0 < s → ∀ (x : P.R.B), IsUnit x → P.φB^[s] x = (l : P.R.B) * x → P.ιB x ∈ Fil P 1 → P.ιB x ∉ Fil P 2 → (∀ j, 0 < j → j < s → ev P j x ∈ Fil P 0 ∧ ev P j x ∉ Fil P 1) → ∀ g : GQ l, ∃ a : ↥(MaximalUnramifiedExtension l), fr l s a = a ∧ P.actQ g x = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B a * x := by
  first | exact @GlobalTheory.PMon.lt_period_conj_ratio | exact GlobalTheory.PMon.lt_period_conj_ratio | (intros; apply GlobalTheory.PMon.lt_period_conj_ratio <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.mooreDeterminant_eq_unramified_mul_period : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (h : ℕ), 0 < h → ∀ a : Fin h → P.R.B, (∀ j, P.φB^[h] (a j) = (l : P.R.B) * a j) → (∀ (i : ℕ) j, ev P i (a j) ∈ Fil P 0) → (Matrix.of fun i j : Fin h => P.φB^[i] (a j)).det ≠ 0 → P.ιB (Matrix.of fun i j : Fin h => P.φB^[i] (a j)).det ∈ Fil P 1 → ∃ κ : ↥(MaximalUnramifiedExtension l), κ ≠ 0 ∧ (Matrix.of fun i j : Fin h => P.φB^[i] (a j)).det = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B κ * P.tB := by
  first | exact @GlobalTheory.PMon.mooreDeterminant_eq_unramified_mul_period_alt | exact GlobalTheory.PMon.mooreDeterminant_eq_unramified_mul_period_alt | (intros; apply GlobalTheory.PMon.mooreDeterminant_eq_unramified_mul_period_alt <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.deRham_blockTriangular_diagonal_blocks : SubQuot := by
  first | exact @GlobalTheory.PMon.subQuot | exact GlobalTheory.PMon.subQuot | (intros; apply GlobalTheory.PMon.subQuot <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

theorem _root_.GlobalTheory.T.jacquet_proUnipotentRadical_fixed_vectors_lift : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α n : Type} [Fintype α] [LinearOrder α] {m : α → Type} [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL n k) V), IsAdmissible π → ∀ y : Jacquet π (unipRad k e), y ∈ fixed (jacU e π) (leviKOne k m) → ∃ v ∈ fixed π (proRad k e), (Submodule.Quotient.mk v : Jacquet π (unipRad k e)) = y := by
  first | exact @GlobalTheory.LocGL.ProRadOnto.exists_proRad_fixed_mk_eq | exact GlobalTheory.LocGL.ProRadOnto.exists_proRad_fixed_mk_eq | (intros; apply GlobalTheory.LocGL.ProRadOnto.exists_proRad_fixed_mk_eq <;> assumption)
end

section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie.CMType

theorem isCMType_conj {E : Type} [Field E] {I : Type} (φ : I → E →+* ℂ)
    (h : Function.Bijective fun i => InfinitePlace.mk (φ i)) :
    IsCMType fun i => ComplexEmbedding.conjugate (φ i) := by
  unfold IsCMType
  intro σ
  have hmk : ∀ j, InfinitePlace.mk (φ j) = InfinitePlace.mk σ ↔
      (σ = ComplexEmbedding.conjugate (φ j) ∨
        σ = ComplexEmbedding.conjugate (ComplexEmbedding.conjugate (φ j))) := by
    intro j
    have cc : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate (φ j)) = φ j := star_star (φ j)
    rw [InfinitePlace.mk_eq_iff, cc]
    constructor
    · rintro (e | e)
      · exact Or.inr e.symm
      · exact Or.inl e.symm
    · rintro (e | e)
      · exact Or.inr e.symm
      · exact Or.inl e.symm
  obtain ⟨i, hi⟩ := h.2 (InfinitePlace.mk σ)
  exact ⟨i, (hmk i).1 hi, fun j hj => h.1 (((hmk j).2 hj).trans hi.symm)⟩

theorem phi_cmType : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R),
    IsCMType (phi H) ∧ ∀ g g', phi H g H.sqrtMinusD = phi H g' H.sqrtMinusD := by
  intro R H
  obtain ⟨_, -, ⟨-, -, -, -, hbij⟩, -, hsq, -⟩ := GlobalTheory.Mem.HostCM.host_cm_embedding_properties R H
  refine ⟨isCMType_conj (embPsi H) hbij, fun g g' => ?_⟩
  show ComplexEmbedding.conjugate (embPsi H g) H.sqrtMinusD =
    ComplexEmbedding.conjugate (embPsi H g') H.sqrtMinusD
  rw [ComplexEmbedding.conjugate_coe_eq, ComplexEmbedding.conjugate_coe_eq, hsq g, hsq g']

end GlobalTheory.LamTie.CMType
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore

namespace GlobalTheory.PtSel

theorem sameChar_eq_one {O₀ O₁ O₂ Γ : Type} [CommRing O₀] [CommRing O₁] [CommRing O₂] [Group Γ]
    {f₁ : O₀ →+* O₁} {f₂ : O₀ →+* O₂} {ψ₁ : Γ →* O₁ˣ} {ψ₂ : Γ →* O₂ˣ}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.SameChar f₁ f₂ ψ₁ ψ₂) (g : Γ) (hg : ψ₁ g = 1) : ψ₂ g = 1 := by
  have h1 := h (Finsupp.single g 1 + Finsupp.single 1 (-1))
  rw [Finsupp.sum_add_index' (by simp) (by intros; simp [add_mul]),
    Finsupp.sum_add_index' (by simp) (by intros; simp [add_mul])] at h1
  simp only [Finsupp.sum_single_index, map_zero, zero_mul, map_one, one_mul, map_neg, hg, Units.val_one,
    mul_one, add_neg_cancel, true_iff] at h1
  ext
  rw [Units.val_one]
  exact add_neg_eq_zero.1 h1

theorem sel_at (hC : GlobalTheory.TwSys.Cheb) (D : D7) (hT : TriplesGood D) (hG : GoodPtRow D) (hR : ResAbsIrr D)
    (a : D.nd.Loc) (ρ : D.nd.X a → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.r) (D.nd.O a))) (π : D.nd.X a)
    (hπ : π ∈ D.nd.Zgood a) (hρ : GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.IsRhoPt D a π (ρ π))
    (j : D.ntw.Tw) (hj : D.ntw.twOf a = j) (k : ℕ) (ψ : Formalism.MainNotions.N.GE D.nd →* (D.ntw.Ok j k)ˣ)
    (f : D.ntw.O0 j →+* D.nd.O a) (hf : HEq f (D.ntw.twist₂ a))
    (hS : GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.SameChar f (BlochKatoReduction.Gen.phiK D.ntw j k) (D.ntw.psiL a) ψ) :
    ∃ s : D.ntw.Sig j, BlochKatoReduction.Gen.goodS (BlochKatoReduction.bk0 D) j s ∧ D.ntw.side _ s = D.ntw.twSide a ∧
      (BlochKatoReduction.Gen.sLen (BlochKatoReduction.bk0 D) j s k (D.nd.Q a) ψ ≠ ⊤ → Br.sFin D.loc D.nbr a ρ π) ∧
      ENNReal.ofReal (Br.sPi D.loc D.nbr a ρ π : ℝ) ≤ BlochKatoReduction.Gen.sLen (BlochKatoReduction.bk0 D) j s k (D.nd.Q a) ψ ∧
      AttachedIn D a π j s := by
  subst hj
  obtain rfl := eq_of_heq hf
  obtain ⟨σ, Sg, hrow, hW, hX⟩ := hG a π hπ
  obtain ⟨s, htr, hgood⟩ := hT a σ Sg hrow hW
  obtain ⟨U, hU⟩ := GlobalTheory.PtCore.twistedRho_conj_latTpsi hC D a π ρ s Sg hρ hX htr (hR a π hπ _ hρ)
  have e1 := GlobalTheory.ConjLatticeSelmer.sPiTop_eq_sTLoc D a π ρ s U hU
  have e2 := GlobalTheory.SelmerSameChar.sTLoc_eq D a s k ψ hS
  have hψ : ∀ v ∈ placesOver D.host.E (D.ntw.l (D.ntw.twOf a)),
      ∀ g ∈ Dec (F := D.host.E) (D.nd.plOm.1 v), ψ g = 1 := by
    intro v hv g hg
    rw [D.ntw.twOf_l] at hv
    exact sameChar_eq_one hS g (D.ntw.psiL_l a v hv _ (D.nd.plOm.2 v) g hg)
  obtain ⟨h1, h2⟩ := GlobalTheory.SelTwistLe.sT_le_sLen D _ s k (D.nd.Q a) ψ hψ
  rw [← e2, ← e1] at h1 h2
  refine ⟨s, hgood, htr.2.1, ?_, ?_, ⟨rfl, σ, Sg, hrow, hW, hX, htr⟩⟩
  · intro hne
    have h3 := h1 hne
    unfold Br.sFin
    rw [lt_top_iff_ne_top]
    intro h4
    exact h3 (by simp only [GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.sPiTop, GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.nlen, h4, if_true])
  · by_cases h4 : Module.length (D.nd.O a) ↥(Br.selPi D.loc D.nbr a ρ π) = ⊤
    · have h5 : BlochKatoReduction.Gen.sLen (BlochKatoReduction.bk0 D) _ s k (D.nd.Q a) ψ = ⊤ := by
        by_contra hne
        exact h1 hne (by simp only [GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.sPiTop, GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.nlen, h4, if_true])
      rw [h5]
      exact le_top
    · exact h2 _ (by simp only [GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.sPiTop, GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.nlen, h4, if_false, Br.sPi])

theorem selCore : GlobalTheory.TwSys.Cheb → ∀ (D : D7) (C : NChoice D), NChTie D C → TriplesGood D → GoodPtRow D →
    ResAbsIrr D → SameTwist D C →
    ∀ ρ : ∀ i : D.nd.Loc, D.nd.X i → (Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.r) (D.nd.O i)),
      (∀ i, ∀ π ∈ D.nd.Zgood i, GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.IsRhoPt D i π (ρ i π)) → SelCore D C ρ := by
  intro hC D C hTie hT hG hR hS ρ hρ i π hπ
  obtain ⟨f, hf, hs⟩ := hS.exists_heq i
  obtain ⟨s, h1, h2, h3⟩ := sel_at hC D hT hG hR i (ρ i) π hπ (hρ i π hπ) _ (hTie.twOf_eq i) _ _ f hf hs
  rw [hTie.Q_eq i] at h3
  exact ⟨s, h1, h2.trans (hTie.twSide_eq i), h3⟩

end GlobalTheory.PtSel

end
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.supercuspidalSupport_of_principalSeries_subquotient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (n : ℕ) (χ : Fin n → kˣ →* ℂˣ) (hχ : ∀ i, IsSmoothChar (χ i)) (π : IrrRep (GL (Fin n) k)), GlobalTheory.SmGL.IsSubquotient π.ρ (prinSeries χ) → HasSupport π.ρ (Finset.univ.val.map fun i => IrrGL.ofChar (χ i) (hχ i)) := by
  first | exact @GlobalTheory.LocLanglands.hasSupport_of_isSubquotient_prinSeries | exact GlobalTheory.LocLanglands.hasSupport_of_isSubquotient_prinSeries | (intros; apply GlobalTheory.LocLanglands.hasSupport_of_isSubquotient_prinSeries <;> assumption)
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocGL

theorem isL_map_tw_of_isL : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [CharZero k] (𝔪 : Multiset (Segment k)) (x : IrrGL (k := k)) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ),
    IsL 𝔪 x.rep → IsL (𝔪.map fun Δ => Δ.tw χ hχ) (x.tw χ hχ).rep := by
  intro k _ _ _ _ _ 𝔪 x χ hχ h
  exact (h.tw χ hχ).of_equiv (x.twEquiv χ hχ)

end GlobalTheory.LocGL
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

noncomputable section

namespace GlobalTheory.SmGL.Segment

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_carrier_nu {Δ : Segment k} {s : ℂ} {x : IrrGL (k := k)} :
    x ∈ (Δ.nu s).carrier ↔ ∃ a : ℕ, a < Δ.len ∧ Δ.first.nu (s + a) = x := by
  rw [mem_carrier]
  show (∃ a : ℕ, a < Δ.len ∧ (Δ.first.nu s).nu a = x) ↔ _
  simp only [IrrGL.nu_nu]

theorem linked_nu_nu_sub_one (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (Δ : Segment k) (t : ℝ) :
    (Δ.nu (t : ℂ)).Linked (Δ.nu ((t - 1 : ℝ) : ℂ)) := by
  have hd : 0 < Δ.first.1 := Δ.isCusp_first.1
  have inj : ∀ r s : ℝ, Δ.first.nu (r : ℂ) = Δ.first.nu (s : ℂ) → r = s :=
    fun r s h => (IrrGL.nu_ofReal_inj hd).1 h
  refine ⟨⟨ofFirst (Δ.first.nu ((t - 1 : ℝ) : ℂ)) (Δ.isCusp_first.nu _) (Δ.len + 1) (Nat.succ_pos _), ?_⟩, ?_, ?_⟩
  · ext x
    rw [Set.mem_union, mem_carrier_nu, mem_carrier_nu, mem_carrier]
    simp only [first_ofFirst, len_ofFirst, IrrGL.nu_nu]
    constructor
    · rintro ⟨a, ha, rfl⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 ha with h | h
      · exact Or.inr ⟨a, h, rfl⟩
      · refine Or.inl ⟨a - 1, by have := Δ.len_pos; omega, ?_⟩
        congr 1
        have h1 : ((a - 1 : ℕ) : ℂ) = (a : ℂ) - 1 := by
          rw [Nat.cast_sub (by have := Δ.len_pos; omega)]; simp
        rw [h1]; push_cast; ring
    · rintro (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩)
      · refine ⟨a + 1, by omega, ?_⟩
        congr 1; push_cast; ring
      · exact ⟨a, by omega, rfl⟩
  · intro hsub
    have hm : Δ.first.nu ((t : ℂ) + ((Δ.len - 1 : ℕ) : ℂ)) ∈ (Δ.nu (t : ℂ)).carrier :=
      mem_carrier_nu.2 ⟨Δ.len - 1, by have := Δ.len_pos; omega, rfl⟩
    obtain ⟨a, ha, he⟩ := mem_carrier_nu.1 (hsub hm)
    have e1 : ((t - 1 : ℝ) : ℂ) + (a : ℂ) = ((t - 1 + a : ℝ) : ℂ) := by push_cast; ring
    have e2 : (t : ℂ) + ((Δ.len - 1 : ℕ) : ℂ) = ((t + ((Δ.len - 1 : ℕ) : ℝ) : ℝ) : ℂ) := by push_cast; ring
    rw [e1, e2] at he
    have h3 := inj _ _ he
    have h4 : (a : ℝ) = ((Δ.len - 1 : ℕ) : ℝ) + 1 := by linarith
    have h5 : a = Δ.len - 1 + 1 := by exact_mod_cast h4
    have := Δ.len_pos
    omega
  · intro hsub
    have hm : Δ.first.nu (((t - 1 : ℝ) : ℂ) + ((0 : ℕ) : ℂ)) ∈ (Δ.nu ((t - 1 : ℝ) : ℂ)).carrier :=
      mem_carrier_nu.2 ⟨0, Δ.len_pos, rfl⟩
    obtain ⟨a, ha, he⟩ := mem_carrier_nu.1 (hsub hm)
    have e1 : (t : ℂ) + (a : ℂ) = ((t + a : ℝ) : ℂ) := by push_cast; ring
    have e2 : ((t - 1 : ℝ) : ℂ) + ((0 : ℕ) : ℂ) = ((t - 1 : ℝ) : ℂ) := by push_cast; ring
    rw [e1, e2] at he
    have h3 := inj _ _ he
    have h4 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    linarith

end GlobalTheory.SmGL.Segment
end
end
