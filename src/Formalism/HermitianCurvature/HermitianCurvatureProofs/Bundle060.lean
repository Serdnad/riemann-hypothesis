module

public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.OpNormLeOneOfIso
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.ConvGrp
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
public import Formalism.HermitianCurvature.Bundle004
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleAtOfAdmissibleList
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle051
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle050
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AeNeZeroComplex
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle048
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle056
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace Formalism.FourierDecayAlt.P.S3dx6

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

theorem unit_of_uh {g : Mx k r} (hg : g ∈ UH (Hpk k r)) : g * g⁻¹ = 1 ∧ g⁻¹ * g = 1 := by
  obtain ⟨-, h2, -⟩ := PI.WBL.Cv.grpAll k r 0
  exact ⟨(h2 g hg).1, (h2 g hg).2.1⟩

theorem inv_inv_uh {g : Mx k r} (hg : g ∈ UH (Hpk k r)) : g⁻¹⁻¹ = g :=
  Matrix.inv_eq_left_inv (unit_of_uh hg).1

theorem inner_sig {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mx k r → (H →L[ℂ] H)}
    (hU : PI.WBL.Cv.SigU σ) {a : Mx k r} (ha : a ∈ UH (Hpk k r)) (u v : H) :
    ⟪σ a u, v⟫_ℂ = ⟪u, σ a⁻¹ v⟫_ℂ := by
  let T : H →ₗᵢ[ℂ] H := { toLinearMap := (σ a : H →ₗ[ℂ] H), norm_map' := hU.2.2 a ha }
  have hai : a⁻¹ ∈ UH (Hpk k r) := WeylGroupFacts.uh_inv ha
  have hv : σ a (σ a⁻¹ v) = v := by
    rw [← ContinuousLinearMap.comp_apply, ← hU.2.1 a ha _ hai, (unit_of_uh ha).1, hU.1]; rfl
  calc ⟪σ a u, v⟫_ℂ = ⟪T u, T (σ a⁻¹ v)⟫_ℂ := by
        show ⟪σ a u, v⟫_ℂ = ⟪σ a u, σ a (σ a⁻¹ v)⟫_ℂ
        rw [hv]
    _ = ⟪u, σ a⁻¹ v⟫_ℂ := T.inner_map_map _ _

theorem norm_psi (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (g : Mx k r) : ‖psi k r z c g‖ = 1 := by
  unfold psi
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

theorem measurePreserving_invM_of_isHaarOn {z : Fin (2 * r + k + 1) → ℂ} {μ : Measure (Mt k r)} (h : B.IsHaarOn (UWset k r z) μ) :
    MeasurePreserving (B7.invM (k := k) (r := r)) μ μ :=
  ⟨B7.measurable_invM, Formalism.FourierDecayAlt.P.haar_measure_inversion k r _ μ (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z) h⟩

theorem mp_inv_N {μ : Measure (Mt k r)} (h : B.IsHaarOn (Nset k r) μ) :
    MeasurePreserving (B7.invM (k := k) (r := r)) μ μ :=
  ⟨B7.measurable_invM, Formalism.FourierDecayAlt.P.haar_measure_inversion k r _ μ (Formalism.FourierDecayAlt.P.unipotent_radical_closed k r) h⟩

end Formalism.FourierDecayAlt.P.S3dx6
end
end

section

open Matrix MeasureTheory Filter

noncomputable section

namespace Formalism.FourierDecayAlt.P.WordKeyIdentity

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem int_list_smul' {α ι E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (μ : Measure α) (l : List ι) (a : ι → ℂ) (φ : ι → α → E) (h : ∀ i ∈ l, Integrable (φ i) μ) :
    Integrable (fun p => (l.map fun i => a i • φ i p).sum) μ ∧
      ∫ p, (l.map fun i => a i • φ i p).sum ∂μ = (l.map fun i => a i • ∫ p, φ i p ∂μ).sum := by
  induction l with
  | nil => simp
  | cons i l ih =>
    have hi : Integrable (φ i) μ := h i (by simp)
    obtain ⟨hl1, hl2⟩ := ih (fun j hj => h j (by simp [hj]))
    have hadd := integral_add (hi.smul (a i)) hl1
    simp only [Pi.smul_apply] at hadd
    simp only [List.map_cons, List.sum_cons]
    refine ⟨(hi.smul (a i)).add hl1, ?_⟩
    rw [hadd, integral_smul, hl2]

theorem int_list_smul {α ι E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (μ : Measure α) (l : List ι) (a : ι → ℂ) (φ : ι → α → E) (h : ∀ i ∈ l, Integrable (φ i) μ) :
    ∫ p, (l.map fun i => a i • φ i p).sum ∂μ = (l.map fun i => a i • ∫ p, φ i p ∂μ).sum :=
  (int_list_smul' μ l a φ h).2

theorem smul_list_smul {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (c : ℂ) (l : List ι) (a : ι → ℂ)
    (x : ι → E) : c • (l.map fun i => a i • x i).sum = (l.map fun i => a i • (c • x i)).sum := by
  induction l with
  | nil => simp
  | cons i l ih => simp [smul_add, ih, smul_comm c (a i)]

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem glev0 {g : Mat k r} (hg : g ∈ GV k r) : g ∈ Q.Glev k r 0 :=
  ⟨hg, fun a ha => by simp at ha⟩

theorem word_key (hW : JWords) (hR : RwRho) (D : RealPlaceData k r Wp Wq) {A : ℝ} {m : ℕ}
    {F : Mat k r → (Wq →L[ℂ] Wp)} (hT : TransportedAlt k r A m) (hF : InCC A m F) {g : Mat k r} (hg : g ∈ Om k r D.z D.z')
    (w : List (Mat k r)) (hw : ∀ X ∈ w, unitLie k r X) (hl : w.length ≤ m) :
    Integrable (fun p => xiP D p • Rw w (rho D p F) g) D.μSS ∧
      Rw w (JF D F) g = ∫ p, xiP D p • Rw w (rho D p F) g ∂D.μSS := by
  have hCk : CkOn (m : ℕ∞) (GV k r) F := hF.choose_spec.1
  obtain ⟨hI, hE⟩ := (hW k r Wp Wq D A m F hT hF).2 [] w (by simp) hw (by simpa using hl) g hg
  simp only [List.map_nil] at hI hE
  have hae : (fun p => xiP D p • rho D p (dLR [] (w.map (AdR p)) F) g) =ᵐ[D.μSS]
      fun p => xiP D p • Rw w (rho D p F) g := by
    filter_upwards [B5.ae_inSS D] with p hp
    have := hR k r Wp Wq D m F p hp hCk [] w (by simp) (fun X hX => (hw X hX).1) (by simpa using hl) g hg.1
    simp only [List.map_nil] at this
    rw [← this]
    rfl
  exact ⟨hI.congr hae, by rw [← integral_congr_ae hae]; exact hE⟩

end Formalism.FourierDecayAlt.P.WordKeyIdentity

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem capelli_under_integral_of_parts : Formalism.FourierDecayAlt.JF.CVUnderIntOfParts := by
  intro hW hWS hR k r Wp Wq _ _ _ _ _ _ D A m F Y hnm hT hF g hg
  obtain ⟨L, hLw, hLeq⟩ := hWS k r Y
  have hCk : CkOn (m : ℕ∞) (GV k r) F := hF.choose_spec.1
  have hCkn : CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (GV k r) F := B5.ckOn_mono (by exact_mod_cast hnm) hCk
  have hJck : CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (Om k r D.z D.z') (JF D F) := by
    intro g₀ hg₀
    obtain ⟨U, F', hU, hgU, hc, he⟩ := (hW k r Wp Wq D A m F hT hF).1 g₀ ⟨WordKeyIdentity.glev0 hg₀.1, hg₀.2⟩
    exact ⟨U, F', hU, hgU, hc.of_le (by exact_mod_cast hnm), fun x hx hxG => he x hx (WordKeyIdentity.glev0 hxG)⟩
  rw [hLeq _ _ _ hJck g hg hg.1]
  have key : ∀ cw ∈ L, Integrable (fun p => xiP D p • Rw cw.2 (rho D p F) g) D.μSS ∧
      Rw cw.2 (JF D F) g = ∫ p, xiP D p • Rw cw.2 (rho D p F) g ∂D.μSS := fun cw hcw =>
    WordKeyIdentity.word_key hW hR D hT hF hg cw.2 (hLw cw hcw).1 ((hLw cw hcw).2.trans hnm)
  have hRHS : (∫ p, xiP D p • Q.CV k r Y (rho D p F) g ∂D.μSS) =
      ∫ p, (L.map fun cw => cw.1 • (xiP D p • Rw cw.2 (rho D p F) g)).sum ∂D.μSS := by
    refine integral_congr_ae ?_
    filter_upwards [B5.ae_inSS D] with p hp
    rw [hLeq _ _ _ (B5.ckOn_rho D hp hCkn) g hg.1 hg.1, WordKeyIdentity.smul_list_smul]
  rw [hRHS, WordKeyIdentity.int_list_smul D.μSS L (fun cw => cw.1) (fun cw p => xiP D p • Rw cw.2 (rho D p F) g)
    fun cw hcw => (key cw hcw).1]
  refine congrArg List.sum (List.map_congr_left fun cw hcw => ?_)
  rw [(key cw hcw).2]

end Formalism.FourierDecayAlt.P
end
end

section

namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

theorem onOld_id {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {w : List C.Letter} :
    ∀ (ys : List ℝ) (x : Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat k ρ → (Wq →L[ℂ] Wp)),
      KB.onOld (⇑(LinearMap.id : (Wd.Ix (Fin w.length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) →ₗ[ℂ] _)) ys x = x
  | [], x => rfl
  | y :: ys, x => by
    funext e
    simp only [KB.onOld]
    rw [onOld_id ys]
    exact congrArg x (Fin.cons_self_tail e)

theorem mix_push {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
    [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (ε : ℝ) (i : ℕ) {K d : ℕ}
    (grid : Fin K → Fin (d + 1) → ℝ) (mk : List ℝ → List C.Letter) (p q : C.LPt) :
    KB.mix S v ε i (PBD.pushU grid mk) (PBD.pushTh grid mk) p q =
      ∑ n : Fin K → Fin (d + 1), (F7.thGrid grid n : ℂ) *
        KB.gN S v ε i (mk (List.ofFn fun b => grid b (n b))) p q := by
  unfold KB.mix PBD.pushTh
  simp only [Complex.ofReal_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hmem : mk (List.ofFn fun b => grid b (n b)) ∈ PBD.pushU grid mk :=
    Finset.mem_image_of_mem _ (Finset.mem_univ n)
  rw [Finset.sum_eq_single_of_mem _ hmem]
  · simp
  · intro b _ hb
    rw [if_neg (Ne.symm hb)]
    simp

section sizes

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

theorem sizeAt_plusW (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (ys : List ℝ) (a : List C.Letter) :
    S.sizeAt v (KB.plusW ys a) = (ys.map fun y => |S.P v y|).prod * S.sizeAt v a := by
  unfold C.HidaSetting.sizeAt
  rw [PBD.plusW_eq, List.map_append, List.prod_append, List.map_map]
  rfl

theorem sizeAt_minusW (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (ys : List ℝ) (a : List C.Letter) :
    S.sizeAt v (KB.minusW ys a) = (ys.map fun y => |S.P v (y + 1)|).prod * S.sizeAt v a := by
  unfold C.HidaSetting.sizeAt
  rw [PBD.minusW_eq, List.map_append, List.prod_append, List.map_map]
  rfl

theorem sizeAt_pos (S : C.HidaSetting E Wp Wq) (hG : C.GridsOK S) (v : Fin S.f) (a : List C.Letter)
    (ha : D.AdmAt S v a) : 0 < S.sizeAt v a := by
  obtain ⟨w, hw⟩ := ha
  have hA := (PBD.admissible_list_of_word S w v).1
  rw [hw] at hA
  unfold C.HidaSetting.sizeAt
  refine List.prod_pos fun x hx => ?_
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hl
  have hnode := hA j hj
  have hgrid : (∃ a', PBD.nodeOf a[j] ∈ S.grid v a') ∨ PBD.nodeOf a[j] ∈ S.grid1 v := by
    rcases Finset.mem_union.1 hnode with h | h
    · exact Or.inl ⟨_, h⟩
    · exact Or.inr h
  obtain ⟨-, -, hP, hP1⟩ := (hG v).2.2.2.2.2 _ hgrid
  refine abs_pos.2 ?_
  unfold PBD.nodeOf at hP hP1
  split_ifs at hP hP1 with hs
  · exact hP
  · simpa using hP1

end sizes

section nodes

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

def NodeOK (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (a : List C.Letter) (one : Bool) (y : ℝ) : Prop :=
  (one = false ∧ ∃ a', a.length < a' ∧ a' ≤ S.Ntop ∧ y ∈ S.grid v a') ∨
    (one = true ∧ y ∈ S.grid1 v ∧ ∀ x ∈ a, PBD.Sep (true, y) x)

theorem nodes_level (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (v : Fin S.f) (a : List C.Letter) (ha : D.AdmAt S v a)
    (K : ℕ) (hK : a.length + K ≤ S.Ntop) (j : ℕ) (hj : j ≤ S.G.r) :
    ∃ grid : Fin K → Fin (2 * j + 1) → ℝ,
      (∀ b, Function.Injective (grid b)) ∧
      (∀ b, ∑ i, |F7.lagCo (grid b) i| ≤ (28 * (S.Ntop : ℝ) / (S.cutHi v - S.cutLo v)) ^ (2 * j)) ∧
      (∀ n : Fin K → Fin (2 * j + 1),
        D.AdmAt S v (KB.plusW (List.ofFn fun b => grid b (n b)) a) ∧
        D.AdmAt S v (KB.minusW (List.ofFn fun b => grid b (n b)) a) ∧
        KB.CutWord (D.parOf S v) (S.l + 1) (KB.plusW (List.ofFn fun b => grid b (n b)) a) ∧
        KB.CutWord (D.parOf S v) (S.l + 1) (KB.minusW (List.ofFn fun b => grid b (n b)) a) ∧
        (List.ofFn fun b => grid b (n b)).Pairwise (fun y y' => 2 < |y - y'|) ∧
        ∀ y ∈ (List.ofFn fun b => grid b (n b)), NodeOK S v a (decide (j = 0)) y) ∧
      KB.LocProb S v (a.length + K) (PBD.pushU grid fun ys => KB.plusW ys a)
        (PBD.pushTh grid fun ys => KB.plusW ys a) ∧
      KB.LocProb S v (a.length + K) (PBD.pushU grid fun ys => KB.minusW ys a)
        (PBD.pushTh grid fun ys => KB.minusW ys a) := by
  have hB' := hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGo, hGr, -⟩ := hB'
  have hCI := PBCut.cutInside_of_built hB
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  ·
    obtain ⟨ys, hlen, -, hg1, hp, hm, hcp, hcm, hpw⟩ :=
      Formalism.FourierDecayAlt.P.new_letters_admissible_level_one E Wp Wq S hGo hGr hCI v a K ha hK
    set grid : Fin K → Fin (2 * 0 + 1) → ℝ := fun b _ => ys.get ⟨b, by rw [hlen]; exact b.2⟩ with hgrid
    have hys : ∀ n : Fin K → Fin (2 * 0 + 1), (List.ofFn fun b => grid b (n b)) = ys := by
      intro n
      apply List.ext_get
      · simp [hlen]
      · intro i h1 h2
        simp [hgrid]
    have hsep : ∀ y ∈ ys, ∀ x ∈ a, PBD.Sep (true, y) x := by
      obtain ⟨w, hw⟩ := hp
      have hA := (PBD.admissible_list_of_word S w v).2
      rw [hw, PBD.plusW_eq] at hA
      intro y hy x hx
      exact (List.pairwise_append.1 hA).2.2 _ (List.mem_map.2 ⟨y, hy, rfl⟩) _ hx
    have hmk : ∀ mk : List ℝ → List C.Letter, (mk ys = KB.plusW ys a ∨ mk ys = KB.minusW ys a) →
        ∀ n : Fin K → Fin (2 * 0 + 1), D.AdmAt S v (mk (List.ofFn fun b => grid b (n b))) ∧
          (mk (List.ofFn fun b => grid b (n b))).length ≤ a.length + K := by
      intro mk hmk n
      rw [hys n]
      rcases hmk with h | h <;> rw [h]
      · exact ⟨hp, by rw [PBD.plusW_eq]; simp [hlen]; omega⟩
      · exact ⟨hm, by rw [PBD.minusW_eq]; simp [hlen]; omega⟩
    refine ⟨grid, fun b => fun i i' _ => Fin.ext (by have := i.isLt; have := i'.isLt; omega), fun b => ?_, fun n => ?_, ?_, ?_⟩
    · simp [F7.lagCo]
    · rw [hys n]
      refine ⟨hp, hm, hcp, hcm, hpw.imp fun h => by linarith, fun y hy => Or.inr ⟨rfl, hg1 y hy, hsep y hy⟩⟩
    · exact PBD.locProb_push S v _ grid (fun b => fun i i' _ => Fin.ext (by have := i.isLt; have := i'.isLt; omega)) _
        (hmk (fun ys => KB.plusW ys a) (Or.inl rfl))
    · exact PBD.locProb_push S v _ grid (fun b => fun i i' _ => Fin.ext (by have := i.isLt; have := i'.isLt; omega)) _
        (hmk (fun ys => KB.minusW ys a) (Or.inr rfl))
  ·
    obtain ⟨-, grid, hinj, hl1, hmem, hall, hlp, hlm⟩ :=
      Formalism.FourierDecayAlt.P.new_letters_admissible E Wp Wq S hGo hGr hCI v a K (2 * j) ha hK (by omega)
    refine ⟨grid, hinj, hl1, fun n => ?_, hlp, hlm⟩
    obtain ⟨h1, h2, h3, h4, h5⟩ := hall n
    refine ⟨h1, h2, h3, h4, h5.imp fun h => by linarith, fun y hy => Or.inl ⟨by simp; omega, ?_⟩⟩
    obtain ⟨b, rfl⟩ := List.mem_ofFn.1 hy
    exact ⟨a.length + K - b, by omega, by omega, hmem b (n b)⟩

end nodes

end

end Formalism.FourierDecayAlt.P.PBL
end

section

namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

theorem prod_ofFn_map {K : ℕ} (f : Fin K → ℝ) (g : ℝ → ℝ) : ((List.ofFn f).map g).prod = ∏ b, g (f b) := by
  rw [List.map_ofFn, List.prod_ofFn]; rfl

section blockK

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

theorem sW_eq (S : C.HidaSetting E Wp Wq) (j : ℕ) (l : ℂ) :
    sW S j l = Complex.I * (((2 * Real.pi / ((S.g : ℝ) * lamS S j)) : ℝ) : ℂ) * l := rfl

end blockK

end

end Formalism.FourierDecayAlt.P.PBL
end

section

namespace Formalism.FourierDecayAlt.P.GermRateSplit

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate InnerProductSpace

noncomputable section

def qU : ℝ := ((Real.toNNReal (‖U.betaU‖ / (2 * Real.pi)) : NNReal) : ℝ)

section pts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

def lam1 (S : C.HidaSetting E Wp Wq) (s : ℕ) : ℂ := ((((S.g : ℝ) / (2 * Real.pi)) ^ s : ℝ) : ℂ) * Complex.I ^ (s - 2)

def lam2 (S : C.HidaSetting E Wp Wq) (s : ℕ) : ℂ :=
  ((((S.g : ℝ) / (2 * Real.pi)) ^ (s - 1) : ℝ) : ℂ) * Complex.I ^ (s - 1)

def omN (S : C.HidaSetting E Wp Wq) (N : ℕ) (P : C.LPt) : ℝ :=
  √(PBL.nnS S P) / PBL.bS S P * √(Top.wPt (S.T * S.T') S.G.r (PBL.stdS S P) ^ N)

end pts

end

end Formalism.FourierDecayAlt.P.GermRateSplit
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem jAFFStable_of_parts (hG : GermOps) (hE : ExtLoc) (hS : SmoothOps) (hA : AdjComm) (hQ : EquivOps)
    (hO : OmPDom) : JAFFStable := by
  refine ⟨0, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ _ v Θ hΘ J hJ
  obtain ⟨hDom, hPos⟩ := hO E Wp Wq S T v
  have hG' := hG S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) Θ
  have hsupp : ∀ f' : B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)), tsupport f' ⊆ OmP S T v →
      B.SuppIn (B.GPos (T v).base) f' := by
    intro f' hs x hx
    have hxG : x ∈ B.GV S.G.k S.G.r :=
      (Formalism.FourierDecayAlt.P.B5.GV_closed (k := S.G.k) (r := S.G.r)).closure_subset_iff.2 (by exact fun y hy => hy.1) hx
    have hxT : x ∈ tsupport f' := closure_mono (by exact fun y hy => hy.2) hx
    exact hPos x (hs hxT) hxG
  constructor
  · refine hQ hE _ _ _ _ (T v).base (OmP S T v) (B.opApply Θ) hDom
      (fun U f₁ f₂ hU he g hg hgG => (hG'.1 U f₁ f₂ hU he g hg hgG).1) (fun c f₁ g _ => (hG'.2 c f₁ g).1)
      (fun f₁ hf hs => (hS _ _ _ _ (T v).base Θ _ hDom.1 hPos hΘ.1 f₁ hf hs).1) ?_ J hJ
    intro f₁ hf _ _ p hp g hg hgG
    exact hΘ.2 p hp f₁ (Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top hf) g (hPos g hg hgG)
  · refine hQ hE _ _ _ _ (T v).base (OmP S T v) (B.opAdj Θ) hDom
      (fun U f₁ f₂ hU he g hg hgG => (hG'.1 U f₁ f₂ hU he g hg hgG).2) (fun c f₁ g _ => (hG'.2 c f₁ g).2)
      (fun f₁ hf hs => (hS _ _ _ _ (T v).base Θ _ hDom.1 hPos hΘ.1 f₁ hf hs).2) ?_ J hJ
    intro f₁ hf hc hs p hp g hg hgG
    exact hA _ _ _ _ (T v).base Θ hΘ.1 hΘ.2 f₁ hf hc (hsupp f₁ hs) p hp g (hPos g hg hgG)

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS
end
