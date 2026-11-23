module

public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Formalism.LocalToGlobal.IndefiniteReal.PeterssonHilbertSpace
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Monotonicity.Lemmas
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

noncomputable section

namespace Formalism.IndefR.FWT

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct nonZeroDivisors

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

end Gen

section Map

open MvPolynomial

end Map

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult
  Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar



variable {D : D7}

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem Q_base_empty (R : RealDat D A Ks) (hL : R.toLevCh.Is A.μ0) : R.Q A.μ0 = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun PP hPP => ?_
  have h := (hL.Q_ram A.μ0 PP).2 (Or.inl hPP)
  rw [hL.xi_base] at h
  exact h fun x _ => rfl

section Phi

variable (R : RealDat D A Ks) (i : Fin D.R.m) {K' : Type} [Field K'] (σ' : K' →+* ℂ) (t : T0)
  {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E))
  (N : Submodule (𝓞 D.host.E) La)

end Phi

section Reps

variable (R : RealDat D A Ks) (i : Fin D.R.m) (t : T0)

end Reps

section Place

variable (R : RealDat D A Ks) (i : Fin D.R.m) (t : T0) {Cl : Type} [Fintype Cl] (h : Cl → GA D (Vc D i))
  {K' : Type} [Field K'] {jL : D.what₂.LL →+* K'} {σ' : K' →+* ℂ}

theorem levFn_flag1_mem {n : ℕ} (β : GL (Fin n) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ n) (S : Subfield ℂ)
    (hcg : ∀ c, ∀ PP ∈ L.Pg, ∀ u, ((L.cg c PP u : ℂˣ) : ℂ) ∈ S) (hxq : ∀ PP ∈ L.Q, ∀ u, ((L.xq PP u : ℂˣ) : ℂ) ∈ S)
    (x : GL (Fin n) (Lev.EAf D)) :
    ((Formalism.L2.DIV.levFn β (Lev.flag1L L) x : ℂˣ) : ℂ) ∈ S := by
  unfold Formalism.L2.DIV.levFn
  simp only [Units.val_mul, Units.coe_prod]
  refine S.mul_mem (S.mul_mem ?_ (S.prod_mem fun PP hPP => S.prod_mem fun c _ => hcg _ _ hPP _))
    (S.prod_mem fun PP hPP => hxq _ hPP _)
  unfold Formalism.L2.DIV.ext1
  split_ifs
  · have e : (Lev.flag1L L).P.chi = 1 := rfl
    rw [e, MonoidHom.one_apply, Units.val_one]
    exact S.one_mem
  · simp only [Units.val_one]
    exact S.one_mem



theorem hχ_of (hchi : ∀ PP ∈ R.Pg, ∀ u, ∃ a, ((R.chi ((i : ℕ) + 1) PP u : ℂˣ) : ℂ) = D.what₂.embLL a)
    (hxi : ∀ PP ∈ R.Q t, ∀ u, ∃ a, ((R.xiR t PP u : ℂˣ) : ℂ) = D.what₂.embLL a) :
    ∀ k, ∃ a, (((levEnvOf (Vc D i) (R.βV i) (R.toLevCh.datVt i t) R.pl (A.ok t)).lev.χ k : ℂˣ) : ℂ) = D.what₂.embLL a := by
  intro k
  have hcg : ∀ c, ∀ PP ∈ (R.toLevCh.datVt i t).Pg, ∀ u,
      (((R.toLevCh.datVt i t).cg c PP u : ℂˣ) : ℂ) ∈ D.what₂.embLL.fieldRange := by
    intro c PP hPP u
    have e : (R.toLevCh.datVt i t).cg c PP u = (R.chi ((i : ℕ) + 1) PP u)⁻¹ := by
      simp [LevCh.datVt, Lev.datY]
    rw [e, Units.val_inv_eq_inv_val]
    obtain ⟨a, ha⟩ := hchi PP hPP u
    exact Subfield.inv_mem _ ⟨a, ha.symm⟩
  have hxq : ∀ PP ∈ (R.toLevCh.datVt i t).Q, ∀ u,
      (((R.toLevCh.datVt i t).xq PP u : ℂˣ) : ℂ) ∈ D.what₂.embLL.fieldRange := by
    intro PP hPP u
    have e : (R.toLevCh.datVt i t).xq PP u = R.xiR t PP u := by
      simp [LevCh.datVt, Lev.datY]
    rw [e]
    obtain ⟨a, ha⟩ := hxi PP hPP u
    exact ⟨a, ha.symm⟩
  obtain ⟨a, ha⟩ := levFn_flag1_mem (R.βV i) (R.toLevCh.datVt i t) D.what₂.embLL.fieldRange hcg hxq _
  exact ⟨a, ha.symm⟩

end Place

section Assemble

end Assemble

end Formalism.IndefR.FWT

end
end

section

noncomputable section

open Matrix

namespace Formalism.IndefR.Datum

end Formalism.IndefR.Datum

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum
open scoped TensorProduct

namespace Formalism.IndefR.Datum.Brg

section Gen
variable {R : Type*} [CommRing R] (c : R →+* R) {n m : ℕ}

theorem hO_tr (I : Matrix (Fin n) (Fin n) R) (K : Matrix (Fin m) (Fin m) R) (x y : Matrix (Fin m) (Fin n) R) :
    ∑ a, ∑ b, ∑ c', ∑ d, I a b * c (y c' b) * K c' d * x d a = (I * (y.map c)ᵀ * K * x).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  calc ∑ b, ∑ c', ∑ d, I a b * c (y c' b) * K c' d * x d a
      = ∑ b, ∑ d, ∑ c', I a b * c (y c' b) * K c' d * x d a :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ d, ∑ b, ∑ c', I a b * c (y c' b) * K c' d * x d a := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem small_gen (G I : Matrix (Fin n) (Fin n) R) (K : Matrix (Fin m) (Fin m) R) (hIG : I * G = 1)
    (hI : (I.map c)ᵀ = I) (x y : Matrix (Fin m) (Fin n) R) :
    ∑ i, ∑ j, ∑ k, ∑ l, c ((y * I)ᵀ i j) * G k i * K j l * (x * I)ᵀ k l =
      ∑ a, ∑ b, ∑ c', ∑ d, I a b * c (y c' b) * K c' d * x d a := by
  rw [sum_eq_trace, hO_tr, ← Matrix.trace_transpose]
  have e : ((y * I)ᵀ).map c = I * (y.map c)ᵀ := by
    rw [Matrix.transpose_map, Matrix.map_mul, Matrix.transpose_mul, hI]
  rw [e]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  calc _ = (K * (x * ((I * G) * I * (y.map c)ᵀ))).trace := by simp only [Matrix.mul_assoc]
    _ = ((K * x) * (I * (y.map c)ᵀ)).trace := by rw [hIG, Matrix.one_mul]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]

theorem inv_gen (G I g g' : Matrix (Fin n) (Fin n) R) (hIG : I * G = 1) (hGI : G * I = 1) (hg : g * g' = 1)
    (h : (g.map c)ᵀ * G * g = G) : g' * I = I * (g.map c)ᵀ := by
  calc g' * I = (I * G) * g' * I := by rw [hIG, Matrix.one_mul]
    _ = I * ((g.map c)ᵀ * G * g) * g' * I := by rw [h]
    _ = I * (g.map c)ᵀ * (G * (g * g') * I) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hg, Matrix.mul_one, hGI, Matrix.mul_one]

theorem small_act (I g g' : Matrix (Fin n) (Fin n) R) (k : Matrix (Fin m) (Fin m) R) (h : g' * I = I * (g.map c)ᵀ)
    (x : Matrix (Fin m) (Fin n) R) : (k * x * g' * I)ᵀ = g.map c * (x * I)ᵀ * kᵀ := by
  rw [Matrix.mul_assoc (k * x), h]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

theorem large_gen (hc : ∀ a, c (c a) = a) (G I : Matrix (Fin n) (Fin n) R) (K : Matrix (Fin m) (Fin m) R)
    (hGI : G * I = 1) (hI : (I.map c)ᵀ = I) (hK : (K.map c)ᵀ = K) (x y : Matrix (Fin m) (Fin n) R) :
    ∑ i, ∑ j, ∑ k, ∑ l, c ((I * (y.map c)ᵀ)ᵀ i j) * K k i * G j l * (I * (x.map c)ᵀ)ᵀ k l =
      c (∑ a, ∑ b, ∑ c', ∑ d, I a b * c (y c' b) * K c' d * x d a) := by
  have e0 : (y.map c).map c = y := by ext i j; simp [hc]
  have t : ∀ M : Matrix (Fin n) (Fin n) R, c M.trace = ((M.map c)ᵀ).trace := by
    intro M; simp [Matrix.trace, map_sum]
  have e : ((I * (y.map c)ᵀ)ᵀ).map c = y * I := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.map_mul, e0, Matrix.transpose_map, hI]
  have e2 : ((I * (y.map c)ᵀ * K * x).map c)ᵀ = (x.map c)ᵀ * K * y * I := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_mul, hI, hK, Matrix.transpose_map, e0, Matrix.transpose_transpose]
    simp only [Matrix.mul_assoc]
  rw [sum_eq_trace, hO_tr, t, e2, ← Matrix.trace_transpose, e]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  calc _ = ((G * I) * ((x.map c)ᵀ * K * y * I)).trace := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hGI, Matrix.one_mul]

theorem large_act (I g g' : Matrix (Fin n) (Fin n) R) (k : Matrix (Fin m) (Fin m) R) (h : g * I = I * (g'.map c)ᵀ)
    (x : Matrix (Fin m) (Fin n) R) :
    (I * ((k * x * g').map c)ᵀ)ᵀ = k.map c * (I * (x.map c)ᵀ)ᵀ * gᵀ := by
  have k' : g'.map c * Iᵀ = Iᵀ * gᵀ := by
    have := congrArg Matrix.transpose h
    simpa [Matrix.transpose_mul] using this.symm
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.map_mul, Matrix.mul_assoc]
  rw [k']

end Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev GG (S : HSp D) : Matrix (Fin S.rank) (Fin S.rank) (AE D) := S.gram.map (incA D)
abbrev GI (S : HSp D) : Matrix (Fin S.rank) (Fin S.rank) (AE D) := (S.gram⁻¹).map (incA D)

theorem cA_inc (a : D.host.E) : cA D (incA D a) = incA D (star a) := by
  simp [cA, sigR, CMData.sig, inclR]; rfl

theorem gram_herm (S : HSp D) : S.gramᴴ = S.gram :=
  Matrix.ext fun i j => S.herm.eq _ _

theorem GG_GI (S : HSp D) : GG S * GI S = 1 := by
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (gram_det_ne S))]
  simp

theorem GI_GG (S : HSp D) : GI S * GG S = 1 := by
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (gram_det_ne S))]
  simp

theorem GI_herm (S : HSp D) : ((GI S).map (cA D))ᵀ = GI S := by
  have h : (S.gram⁻¹)ᴴ = S.gram⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, gram_herm]
  refine Matrix.ext fun i j => ?_
  exact (cA_inc _).trans (congrArg (incA D) (congrFun (congrFun h i) j))

theorem GG_herm (S : HSp D) : ((GG S).map (cA D))ᵀ = GG S := by
  refine Matrix.ext fun i j => ?_
  exact (cA_inc _).trans (congrArg (incA D) (congrFun (congrFun (gram_herm S) i) j))

theorem mt_mul_inv (S : HSp D) (g : GA D S) : Formalism.L2.Theta.mt S g * Formalism.L2.Theta.mt S g⁻¹ = 1 := by
  unfold Formalism.L2.Theta.mt
  rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]

theorem inv_GI (S : HSp D) (g : GA D S) :
    Formalism.L2.Theta.mt S g⁻¹ * GI S = GI S * ((Formalism.L2.Theta.mt S g).map (cA D))ᵀ :=
  inv_gen (cA D) (GG S) (GI S) _ _ (GI_GG S) (GG_GI S) (mt_mul_inv S g) (mt_rel S g)

theorem bridgeSmall : BridgeSmall D := by
  intro S T hr
  refine ⟨fun x y => ?_, fun g h x => ?_⟩
  · have : hHom S T (toTWsmall S T y) (toTWsmall S T x) = hO S T x y := by
      unfold hHom; rw [if_pos hr]
      exact small_gen (cA D) (GG S) (GI S) (GG T) (GI_GG S) (GI_herm S) x y
    unfold symplO sympl; rw [this]
  · unfold actHom; rw [if_pos hr]
    exact small_act (cA D) (GI S) _ _ _ (inv_GI S g) x

theorem trace_cA (a : AE D) :
    Algebra.trace (AF D.host.F) (AE D) (cA D a) = Algebra.trace (AF D.host.F) (AE D) a := by
  let f : AE D →ₐ[AF D.host.F] AE D := Algebra.TensorProduct.map (AlgHom.id _ _) D.sp.cm.sig
  have hf : ∀ a, f a = cA D a := by
    intro a
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul r e => simp [f, cA, sigR]
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
  have hff : f.comp f = AlgHom.id _ _ := AlgHom.ext fun a => by
    rw [AlgHom.comp_apply, hf, hf, cA_cA]; rfl
  let g : AE D ≃ₐ[AF D.host.F] AE D := AlgEquiv.ofAlgHom f f hff hff
  rw [← hf]
  exact Algebra.trace_eq_of_algEquiv g a

theorem bridgeLarge (hxi : star D.host.xi0 = -D.host.xi0) : BridgeLarge D := by
  intro S T hr
  refine ⟨fun x y => ?_, fun g h x => ?_⟩
  · have : hHom T S (toTWlarge S T y) (toTWlarge S T x) = cA D (hO S T x y) := by
      unfold hHom; rw [if_pos hr.le]
      exact large_gen (cA D) cA_cA (GG S) (GI S) (GG T) (GG_GI S) (GI_herm S) (GG_herm T) x y
    unfold symplO sympl
    rw [this, ← trace_cA (incA D D.host.xi0 * hO S T x y), map_mul, cA_inc, hxi, map_neg, neg_mul, map_neg]
  · unfold actHom; rw [if_pos hr.le]
    have k := inv_GI S g⁻¹
    rw [inv_inv] at k
    exact large_act (cA D) (GI S) _ _ _ k x

theorem star_purely_imaginary_eq_neg : star D.host.xi0 = -D.host.xi0 := by
  have hs : ∀ x : D.host.E, D.host.φ₀ (star x) = starRingEnd ℂ (D.host.φ₀ x) := fun x => by
    haveI := D.host.isCMField_hostE
    exact NumberField.IsCMField.complexEmbedding_complexConj D.host.E D.host.φ₀ x
  have hd : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  apply D.host.φ₀.injective
  rw [hs, map_neg]
  unfold Host.xi0
  rw [map_div₀, map_neg, map_one, map_mul, map_natCast, hd]
  simp [div_neg]

theorem bridgeLarge' : BridgeLarge D := bridgeLarge star_purely_imaginary_eq_neg

end Formalism.IndefR.Datum.Brg

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory
open Formalism.L2.Theta

namespace Formalism.IndefR.PeterssonHilbertSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem countable_GQ (V : HSp D) : Countable (GQ V) :=
  Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma (F := D.host.F) (E := D.host.E) D.sp.cm.sig V.gram

theorem measurableMul_GA (V : HSp D) : MeasurableMul (GA D V) :=
  Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA (F := D.host.F) (E := D.host.E) D.sp.cm.sig V.gram

theorem borel_GA (V : HSp D) : BorelSpace (GA D V) :=
  Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA (F := D.host.F) (E := D.host.E) D.sp.cm.sig V.gram

theorem petPos (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (hH : μ.IsHaarMeasure)
    (hF : IsFundamentalDomain (GQ V) 𝓕 μ) : PetPos V μ 𝓕 := by
  intro F hc hinv hne hint
  have := countable_GQ V
  have := measurableMul_GA V
  have := borel_GA V
  have := hH
  set U : Set (GA D V) := {g | F g ≠ 0} with hUdef
  have hUo : IsOpen U := isOpen_ne_fun hc continuous_const
  have hUne : U.Nonempty := by
    by_contra h
    apply hne
    funext g
    by_contra hg
    exact h ⟨g, hg⟩
  have hUpos : 0 < μ U := hUo.measure_pos μ hUne
  have hnn : 0 ≤ᵐ[μ.restrict 𝓕] fun g => ‖F g‖ ^ 2 := ae_of_all _ (fun g => by positivity)
  refine lt_of_le_of_ne (integral_nonneg fun g => by positivity) ?_
  intro h0
  have hz : (fun g => ‖F g‖ ^ 2) =ᵐ[μ.restrict 𝓕] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hnn hint).1 h0.symm
  have hset : {g : GA D V | ¬ (‖F g‖ ^ 2 = (0 : GA D V → ℝ) g)} = U := by
    ext g
    simp [hUdef]
  have hFU : μ (U ∩ 𝓕) = 0 := by
    have h1 := ae_iff.1 hz
    rw [hset, Measure.restrict_apply hUo.measurableSet] at h1
    exact h1
  have key : U ≤ᵐ[μ] (⋃ γ : GQ V, (fun x => (γ : GA D V) * x) ⁻¹' (U ∩ 𝓕) : Set (GA D V)) := by
    filter_upwards [hF.ae_covers] with x hx hxU
    obtain ⟨γ, hγ⟩ := hx
    refine Set.mem_iUnion.2 ⟨γ, ?_, ?_⟩
    · show F ((γ : GA D V) * x) ≠ 0
      rw [hinv _ γ.2 x]
      exact hxU
    · exact hγ
  have hU0 : μ U = 0 := by
    refine le_antisymm ((measure_mono_ae key).trans ?_) bot_le
    refine (measure_iUnion_le _).trans ?_
    simp only [measure_preimage_mul, hFU, tsum_zero, le_refl]
  exact hUpos.ne' hU0

end Formalism.IndefR.PeterssonHilbertSpace

end
end
