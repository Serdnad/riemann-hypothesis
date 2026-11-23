module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1151
public import Formalism.FormalDegreeBessel.StatementG
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Matrix.PosDef
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
import Mathlib.RingTheory.Radical.NatInt
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
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.Bundle001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFrameTranslatedPerpOfIsFrame
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle005
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Mathlib.Algebra.Star.UnitaryStarAlgAut
public import Mathlib.Analysis.Matrix.Hermitian

@[expose] public section

section

noncomputable section

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec
open scoped ContDiff

namespace UpperTheory.Lit.Bur.SmoothConj

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem conj_list_prod {Q Qi : Matrix (Fin n) (Fin n) ℂ} (h1 : Q * Qi = 1) (h2 : Qi * Q = 1)
    (l : List (Matrix (Fin n) (Fin n) ℂ)) :
    Q * l.prod * Qi = (l.map fun g => Q * g * Qi).prod := by
  induction l with
  | nil => simpa using h1
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, ← ih]
    calc Q * (a * l.prod) * Qi = Q * a * 1 * l.prod * Qi := by
          simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = Q * a * Qi * (Q * l.prod * Qi) := by
          rw [← h2]; simp only [Matrix.mul_assoc]

theorem exp_conj_of_inverse {Q Qi : Matrix (Fin n) (Fin n) ℂ} (h1 : Q * Qi = 1) (h2 : Qi * Q = 1)
    (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    NormedSpace.exp (t • (Q * X * Qi)) = Q * NormedSpace.exp (t • X) * Qi := by
  have hi : Qi = Q⁻¹ := (Matrix.inv_eq_right_inv h1).symm
  have hu : IsUnit Q := ⟨⟨Q, Qi, h1, h2⟩, rfl⟩
  subst hi
  rw [← Matrix.exp_conj _ _ hu, Matrix.mul_smul, Matrix.smul_mul]

theorem conj_mem_lieG_of_gram {J G Q Qi X : Matrix (Fin n) (Fin n) ℂ} (h1 : Q * Qi = 1)
    (hg : Qᴴ * J * Q = G) (hX : X ∈ lieG G) : Q * X * Qi ∈ lieG J := by
  have hX' : Xᴴ * G + G * X = 0 := hX
  have hc : Qiᴴ * Qᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
  show (Q * X * Qi)ᴴ * J + J * (Q * X * Qi) = 0
  calc (Q * X * Qi)ᴴ * J + J * (Q * X * Qi)
      = Qiᴴ * Xᴴ * Qᴴ * J * 1 + 1 * J * Q * X * Qi := by
        simp only [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_one, Matrix.one_mul]
    _ = Qiᴴ * Xᴴ * Qᴴ * J * (Q * Qi) + (Qiᴴ * Qᴴ) * J * Q * X * Qi := by rw [h1, hc]
    _ = Qiᴴ * (Xᴴ * (Qᴴ * J * Q) + (Qᴴ * J * Q) * X) * Qi := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hg, hX']; simp

theorem conj_inv_mem_lieG_of_gram {J G Q Qi Y : Matrix (Fin n) (Fin n) ℂ} (h1 : Q * Qi = 1)
    (hg : Qᴴ * J * Q = G) (hY : Y ∈ lieG J) : Qi * Y * Q ∈ lieG G := by
  have hY' : Yᴴ * J + J * Y = 0 := hY
  have hc : Qiᴴ * Qᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
  show (Qi * Y * Q)ᴴ * G + G * (Qi * Y * Q) = 0
  subst hg
  calc (Qi * Y * Q)ᴴ * (Qᴴ * J * Q) + (Qᴴ * J * Q) * (Qi * Y * Q)
      = Qᴴ * Yᴴ * (Qiᴴ * Qᴴ) * J * Q + Qᴴ * J * (Q * Qi) * Y * Q := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Qᴴ * (Yᴴ * J + J * Y) * Q := by
        rw [h1, hc]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_one, Matrix.one_mul]
    _ = 0 := by rw [hY']; simp

theorem smoothVec_conj_of_subset {L L' : Set (Matrix (Fin n) (Fin n) ℂ)}
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) {Q Qi : Matrix (Fin n) (Fin n) ℂ}
    (h1 : Q * Qi = 1) (h2 : Qi * Q = 1) (hL : ∀ X ∈ L', Q * X * Qi ∈ L) {v : H}
    (hv : SmoothVec L σ v) : SmoothVec L' (fun g => σ (Q * g * Qi)) v := by
  intro k Xs hX
  have h := hv k (fun i => Q * Xs i * Qi) fun i => hL _ (hX i)
  have he : ∀ t : Fin k → ℝ, Q * (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod * Qi =
      (List.ofFn fun i => NormedSpace.exp (t i • (Q * Xs i * Qi))).prod := by
    intro t
    rw [conj_list_prod h1 h2, List.map_ofFn]
    congr 1
    congr 1
    funext i
    exact (exp_conj_of_inverse h1 h2 (Xs i) (t i)).symm
  simpa only [he] using h

theorem smoothVec_conj_iff (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    {J G Q Qi : Matrix (Fin n) (Fin n) ℂ} (h1 : Q * Qi = 1) (h2 : Qi * Q = 1)
    (hg : Qᴴ * J * Q = G) (v : H) :
    SmoothVec (lieG G) (fun g => σ (Q * g * Qi)) v ↔ SmoothVec (lieG J) σ v := by
  constructor
  · intro h
    have h' := smoothVec_conj_of_subset (L := lieG G) (L' := lieG J)
      (fun g => σ (Q * g * Qi)) h2 h1 (fun Y hY => conj_inv_mem_lieG_of_gram h1 hg hY) h
    have he : (fun g => σ (Q * (Qi * g * Q) * Qi)) = σ := by
      funext g
      have : Q * (Qi * g * Q) * Qi = g := by
        calc Q * (Qi * g * Q) * Qi = (Q * Qi) * g * (Q * Qi) := by simp only [Matrix.mul_assoc]
          _ = g := by rw [h1]; simp
      rw [this]
    rwa [he] at h'
  · exact smoothVec_conj_of_subset σ h1 h2 fun X hX => conj_mem_lieG_of_gram h1 hg hX

end UpperTheory.Lit.Bur.SmoothConj

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec

theorem _root_.UpperTheory.Lit.Bur.smoothVec_conjugate_unitaryGroup_iff : ∀ {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) {J G Q Qi : Matrix (Fin n) (Fin n) ℂ} (h1 : Q * Qi = 1) (h2 : Qi * Q = 1) (hg : Qᴴ * J * Q = G) (v : H), SmoothVec (lieG G) (fun g => σ (Q * g * Qi)) v ↔ SmoothVec (lieG J) σ v := by
  first | exact @UpperTheory.Lit.Bur.SmoothConj.smoothVec_conj_iff | exact UpperTheory.Lit.Bur.SmoothConj.smoothVec_conj_iff | (intros; apply UpperTheory.Lit.Bur.SmoothConj.smoothVec_conj_iff <;> assumption)
end
end

section

noncomputable section

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec

namespace UpperTheory.Lit.Bur.SmoothTranslate

theorem conj_mem_lieG {n : ℕ} {J g X : Matrix (Fin n) (Fin n) ℂ} (hu : IsUnit g) (hg : g ∈ Formalism.QuantumDeterminants.UH J)
    (hX : X ∈ lieG J) : g⁻¹ * X * g ∈ lieG J := by
  have hd : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).1 hu
  have hAB : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul _ hd
  have hBA : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  have hBA' : (g⁻¹)ᴴ * gᴴ = 1 := by rw [← conjTranspose_mul, hBA, conjTranspose_one]
  have h : gᴴ * J * g = J := hg
  have hX' : Xᴴ * J + J * X = 0 := hX
  show (g⁻¹ * X * g)ᴴ * J + J * (g⁻¹ * X * g) = 0
  calc (g⁻¹ * X * g)ᴴ * J + J * (g⁻¹ * X * g)
      = (g⁻¹ * X * g)ᴴ * (gᴴ * J * g) + (gᴴ * J * g) * (g⁻¹ * X * g) := by rw [h]
    _ = gᴴ * (Xᴴ * ((g⁻¹)ᴴ * gᴴ) * J + J * (g * g⁻¹) * X) * g := by
        simp only [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]
    _ = 0 := by rw [hBA, hBA', Matrix.mul_one, Matrix.mul_one, hX', Matrix.mul_zero, Matrix.zero_mul]

theorem mul_prod_conj {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ} (hu : IsUnit g)
    (l : List (Matrix (Fin n) (Fin n) ℂ)) : g * (l.map fun x => g⁻¹ * x * g).prod = l.prod * g := by
  have hd := (Matrix.isUnit_iff_isUnit_det g).1 hu
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, Matrix.mul_assoc x, ← ih]
    simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul]

theorem smoothVec_translate : ∀ {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {J : Matrix (Fin n) (Fin n) ℂ} (hJ : IsUnit J) {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH J) σ) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH J) {v : H}
    (hv : SmoothVec (lieG J) σ v), SmoothVec (lieG J) σ (σ g v) := by
  intro n H _ _ J hJ σ hσ g hg v hv k Xs hXs
  have hu : IsUnit g := isUnit_of_mem_UH hJ hg
  have hY : ∀ i, g⁻¹ * Xs i * g ∈ lieG J := fun i => conj_mem_lieG hu hg (hXs i)
  have hc : ∀ (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ),
      NormedSpace.exp (t • (g⁻¹ * X * g)) = g⁻¹ * NormedSpace.exp (t • X) * g := fun X t => by
    rw [← Matrix.exp_conj' _ _ hu, Matrix.mul_smul, Matrix.smul_mul]
  have h1 := ((σ g).restrictScalars ℝ).contDiff.comp (hv k _ hY)
  convert h1 using 2 with t
  show σ _ (σ g v) = σ g (σ _ v)
  have hP := expProd_mem_UH hJ hXs t
  have hQ := expProd_mem_UH hJ hY t
  have e1 := hσ.1.2 _ hP _ hg
  have e2 := hσ.1.2 _ hg _ hQ
  have e3 : g * (List.ofFn fun i => NormedSpace.exp (t i • (g⁻¹ * Xs i * g))).prod
      = (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod * g := by
    rw [← mul_prod_conj hu, List.map_ofFn]
    simp only [hc, Function.comp_def]
  have e4 := e1.symm.trans ((congrArg σ e3).symm.trans e2)
  exact congrArg (fun T : H →L[ℂ] H => T v) e4

end UpperTheory.Lit.Bur.SmoothTranslate

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec

theorem _root_.UpperTheory.Lit.Bur.smoothVec_stable_under_unitaryGroup : ∀ {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {J : Matrix (Fin n) (Fin n) ℂ} (hJ : IsUnit J) {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH J) σ) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH J) {v : H} (hv : SmoothVec (lieG J) σ v), SmoothVec (lieG J) σ (σ g v) := by
  first | exact @UpperTheory.Lit.Bur.SmoothTranslate.smoothVec_translate | exact UpperTheory.Lit.Bur.SmoothTranslate.smoothVec_translate | (intros; apply UpperTheory.Lit.Bur.SmoothTranslate.smoothVec_translate <;> assumption)
end
end

section

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec

namespace UpperTheory.Lit.Bur.SobConj

theorem sobCont_conj {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) {J G Q Qi : Matrix (Fin n) (Fin n) ℂ} (h1 : Q * Qi = 1)
    (h2 : Qi * Q = 1) (hg : Qᴴ * J * Q = G) {l : H →ₗ[ℂ] ℂ} (hl : Sobolev₂ (lieG J) σ l) :
    Sobolev₂ (lieG G) (fun g => σ (Q * g * Qi)) l := by
  have back : ∀ a : Matrix (Fin n) (Fin n) ℂ, Q * (Qi * a * Q) * Qi = a := fun a => by
    calc Q * (Qi * a * Q) * Qi = (Q * Qi) * a * (Q * Qi) := by simp only [Matrix.mul_assoc]
      _ = a := by rw [h1, Matrix.one_mul, Matrix.mul_one]
  have lie : ∀ X ∈ lieG J, Qi * X * Q ∈ lieG G := fun X hX =>
    GlobalTheory.SmoothCyclic.conj_lie h2 hg hX
  have e : ∀ X w, dRep (fun g => σ (Q * g * Qi)) (Qi * X * Q) w = dRep σ X w := fun X w => by
    simp only [dRep, GlobalTheory.SmoothCyclic.exp_conj_of_mul h2, back]
  have hsm : ∀ w, SmoothVec (lieG G) (fun g => σ (Q * g * Qi)) w → SmoothVec (lieG J) σ w :=
    fun w hw k Xs hX => by
      simpa only [GlobalTheory.SmoothCyclic.expProd_conj h2, back] using
        hw k (fun i => Qi * Xs i * Q) fun i => lie _ (hX i)
  obtain ⟨S, C, hS, hb⟩ := hl
  refine ⟨S.map fun L => L.map fun X => Qi * X * Q, C, fun L hL X hX => ?_, fun w hw => ?_⟩
  · obtain ⟨L', hL', rfl⟩ := List.mem_map.1 hL
    obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
    exact lie Y (hS L' hL' Y hY)
  · simpa only [e, List.map_map, Function.comp_def, List.foldr_map] using hb w (hsm w hw)

end UpperTheory.Lit.Bur.SobConj

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec

theorem _root_.UpperTheory.Lit.Bur.sobolevCont_of_conj_gram_form : ∀ {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) {J G Q Qi : Matrix (Fin n) (Fin n) ℂ} (h1 : Q * Qi = 1) (h2 : Qi * Q = 1) (hg : Qᴴ * J * Q = G) {l : H →ₗ[ℂ] ℂ} (hl : Sobolev₂ (lieG J) σ l), Sobolev₂ (lieG G) (fun g => σ (Q * g * Qi)) l := by
  first | exact @UpperTheory.Lit.Bur.SobConj.sobCont_conj | exact UpperTheory.Lit.Bur.SobConj.sobCont_conj | (intros; apply UpperTheory.Lit.Bur.SobConj.sobCont_conj <;> assumption)
end

section

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec

namespace UpperTheory.Lit.Bur.Inertia

theorem card_plus_of_congr_Hpk : ∀ {m r : ℕ} (ε : Fin (2 * r + m + 1) → Bool)
    {Q Qi : Matrix (Fin (2 * r + m + 1)) (Fin (2 * r + m + 1)) ℂ} (h1 : Q * Qi = 1) (h2 : Qi * Q = 1)
    (hg : Qᴴ * Formalism.REAL.Jm ε * Q = Formalism.QuantumDeterminants.Hpk m r),
    (Finset.univ.filter fun i => ε i = true).card = m + r := by
  intro m r ε Q Qi h1 h2 hg
  have hu : IsUnit Q := ⟨⟨Q, Qi, h1, h2⟩, rfl⟩
  have hc : Formalism.MainNotions.S.IsCayley m r ε Q := ⟨hu, hg⟩
  exact (ReciprocityTheory.ChartRestriction.DS.Lap.TransportIntA.cayley_signature' hc).1

end UpperTheory.Lit.Bur.Inertia

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec

theorem _root_.UpperTheory.Lit.Bur.sylvester_inertia_signForm_congr_splitHermitian : ∀ {m r : ℕ} (ε : Fin (2 * r + m + 1) → Bool) {Q Qi : Matrix (Fin (2 * r + m + 1)) (Fin (2 * r + m + 1)) ℂ} (h1 : Q * Qi = 1) (h2 : Qi * Q = 1) (hg : Qᴴ * Formalism.REAL.Jm ε * Q = Formalism.QuantumDeterminants.Hpk m r), (Finset.univ.filter fun i => ε i = true).card = m + r := by
  first | exact @UpperTheory.Lit.Bur.Inertia.card_plus_of_congr_Hpk | exact UpperTheory.Lit.Bur.Inertia.card_plus_of_congr_Hpk | (intros; apply UpperTheory.Lit.Bur.Inertia.card_plus_of_congr_Hpk <;> assumption)
end

section

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec

namespace UpperTheory.Lit.Bur.HermCongr


open scoped ComplexOrder in
theorem posDef_of_herm_re_pos {m : ℕ} {J₀ : Matrix (Fin m) (Fin m) ℂ} (hH : J₀ᴴ = J₀)
    (hp : ∀ x : Fin m → ℂ, x ≠ 0 → 0 < (Formalism.QuantumDeterminants.herm J₀ x x).re) : J₀.PosDef := by
  have hA : J₀.IsHermitian := hH
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hA ?_
  intro x hx
  have hre : 0 < (star x ⬝ᵥ J₀ *ᵥ x).re := hp x hx
  have him : (star x ⬝ᵥ J₀ *ᵥ x).im = 0 := hA.im_star_dotProduct_mulVec_self x
  exact Complex.pos_iff.2 ⟨hre, him.symm⟩

theorem exists_congr_one {m : ℕ} {J₀ : Matrix (Fin m) (Fin m) ℂ} (hH : J₀ᴴ = J₀)
    (hp : ∀ x : Fin m → ℂ, x ≠ 0 → 0 < (Formalism.QuantumDeterminants.herm J₀ x x).re) :
    ∃ A Ai : Matrix (Fin m) (Fin m) ℂ, A * Ai = 1 ∧ Ai * A = 1 ∧ Aᴴ * J₀ * A = 1 := by
  have hP := posDef_of_herm_re_pos hH hp
  have hA : J₀.IsHermitian := hH
  have hd : ∀ i, 0 < hA.eigenvalues i := hP.eigenvalues_pos
  set U : Matrix (Fin m) (Fin m) ℂ := (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) with hU
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hUU' : U * star U = 1 := Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hJ : J₀ = U * diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) * star U := by
    have := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  let s : Fin m → ℂ := fun i => ((Real.sqrt (hA.eigenvalues i) : ℝ) : ℂ)
  let t : Fin m → ℂ := fun i => (((Real.sqrt (hA.eigenvalues i))⁻¹ : ℝ) : ℂ)
  have hst : diagonal s * diagonal t = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    have : Real.sqrt (hA.eigenvalues i) ≠ 0 := (Real.sqrt_pos.2 (hd i)).ne'
    simp only [s, t, ← Complex.ofReal_mul, mul_inv_cancel₀ this, Complex.ofReal_one]
  have hts : diagonal t * diagonal s = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    have : Real.sqrt (hA.eigenvalues i) ≠ 0 := (Real.sqrt_pos.2 (hd i)).ne'
    simp only [s, t, ← Complex.ofReal_mul, inv_mul_cancel₀ this, Complex.ofReal_one]
  have htdt : diagonal t * diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) * diagonal t = 1 := by
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    have h0 : Real.sqrt (hA.eigenvalues i) ≠ 0 := (Real.sqrt_pos.2 (hd i)).ne'
    have h1 : Real.sqrt (hA.eigenvalues i) * Real.sqrt (hA.eigenvalues i) = hA.eigenvalues i :=
      Real.mul_self_sqrt (hd i).le
    have h2 : (Real.sqrt (hA.eigenvalues i))⁻¹ * hA.eigenvalues i * (Real.sqrt (hA.eigenvalues i))⁻¹ = 1 := by
      have h3 : ∀ r : ℝ, r ≠ 0 → r⁻¹ * (r * r) * r⁻¹ = 1 := by
        intro r hr
        field_simp
      have h4 := h3 _ h0
      rwa [h1] at h4
    simp only [t]
    exact_mod_cast h2
  have htH : (diagonal t)ᴴ = diagonal t := by
    rw [diagonal_conjTranspose]
    congr 1
    funext i
    simp [t]
  refine ⟨U * diagonal t, diagonal s * star U, ?_, ?_, ?_⟩
  · calc U * diagonal t * (diagonal s * star U) = U * (diagonal t * diagonal s) * star U := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hts, Matrix.mul_one, hUU']
  · calc diagonal s * star U * (U * diagonal t) = diagonal s * (star U * U) * diagonal t := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hUU, Matrix.mul_one, hst]
  · rw [conjTranspose_mul, htH, ← star_eq_conjTranspose]
    calc diagonal t * star U * J₀ * (U * diagonal t)
        = diagonal t * star U * (U * diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) * star U)
            * (U * diagonal t) := by rw [← hJ]
      _ = diagonal t * (star U * U) * diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ))
            * (star U * U) * diagonal t := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hUU, Matrix.mul_one, Matrix.mul_one, htdt]

end UpperTheory.Lit.Bur.HermCongr

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec

theorem _root_.UpperTheory.Lit.Bur.hermitian_form_pos_congruent_identity : ∀ {m : ℕ} {J₀ : Matrix (Fin m) (Fin m) ℂ} (hH : J₀ᴴ = J₀) (hp : ∀ x : Fin m → ℂ, x ≠ 0 → 0 < (Formalism.QuantumDeterminants.herm J₀ x x).re), ∃ A Ai : Matrix (Fin m) (Fin m) ℂ, A * Ai = 1 ∧ Ai * A = 1 ∧ Aᴴ * J₀ * A = 1 := by
  first | exact @UpperTheory.Lit.Bur.HermCongr.exists_congr_one | exact UpperTheory.Lit.Bur.HermCongr.exists_congr_one | (intros; apply UpperTheory.Lit.Bur.HermCongr.exists_congr_one <;> assumption)
end
