module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle019
public import Development.WeilBound.CoreStatements.LocalThetaKernels.LocpairAlg
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.WeilBound.CoreStatements.LocalThetaKernels.IwasAd
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
import Development.WeilBound.CoreStatements.LocalThetaKernels.Locrep
import GroundTheory.GlobalFields.LocalFieldAtPlace
import GroundTheory.LocalFields.PadicLogSeries
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle018
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.LmOfLinBar
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDict
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.Bundle002

@[expose] public section

section

noncomputable section

namespace GlobalTheory.ThK.Dbl.Frame

open scoped Matrix
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix

section Generic

variable {S β : Type} [CommRing S] [Fintype β] [DecidableEq β]

def two : GL β S →* GL (β ⊕ β) S :=
  MonoidHom.mk' (fun g => ⟨fromBlocks g.1 0 0 g.1, fromBlocks (g⁻¹).1 0 0 (g⁻¹).1, by simp [fromBlocks_multiply],
    by simp [fromBlocks_multiply]⟩) fun _ _ => Units.ext (by simp [fromBlocks_multiply])

def wit (a : S) (T : GL β S) : GL (β ⊕ β) S :=
  have h : fromBlocks ((1 - a) • 1) (a • 1) (T⁻¹).1 (-(T⁻¹).1) * fromBlocks 1 (a • T.1) 1 ((a - 1) • T.1) = 1 := by
    rw [fromBlocks_multiply, ← fromBlocks_one]
    simp only [Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.neg_mul, Units.inv_mul]
    refine fromBlocks_inj.2 ⟨?_, ?_, ?_, ?_⟩ <;> module
  ⟨_, _, mul_eq_one_comm.1 h, h⟩

theorem frame_diag (g T : GL β S) (a : S) : (two g * wit a T).1 * (fromRows 1 0 : Matrix (β ⊕ β) β S) = diagCols β * g.1 := by
  change fromBlocks g.1 0 0 g.1 * fromBlocks 1 (a • T.1) 1 ((a - 1) • T.1) * _ = _
  refine Eq.trans ?_ (fromRows_mul 1 1 g.1).symm
  simp [fromBlocks_multiply, fromBlocks_mul_fromRows]

omit [DecidableEq β] in
theorem gram_sym (c : S →+* S) (hc : ∀ z, c (c z) = z) {ε : S} {J : Matrix β β S} (hJ : (J.map c)ᵀ = ε • J) (g : Matrix β β S) :
    ((gᵀ * J * g.map c).map c)ᵀ = ε • (gᵀ * J * g.map c) := by
  have mm : (g.map c).map c = g := Matrix.ext fun i j => hc _
  rw [Matrix.map_mul, Matrix.map_mul, mm, transpose_mul, transpose_mul, hJ, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
  rfl

theorem frame_gram (c : S →+* S) (hc : ∀ z, c (c z) = z) {ε a : S} (hε : ε * ε = 1) (ha : a + c a = 1) {J : Matrix β β S}
    (hJ : (J.map c)ᵀ = ε • J) (g T : GL β S) (hT : g.1ᵀ * J * g.1.map c * T.1.map c = 1) :
    (two g * wit a T).1ᵀ * dbl J * (two g * wit a T).1.map c = fromBlocks 0 1 (ε • 1) 0 := by
  have mm : ∀ X : Matrix β β S, (X.map c).map c = X := fun X => Matrix.ext fun i j => hc _
  set G := g.1ᵀ * J * g.1.map c with hG
  have h1 : (G.map c)ᵀ = ε • G := gram_sym c hc hJ _
  have h2 : T.1ᵀ * G = ε • 1 := by
    have := congrArg (fun X : Matrix β β S => ε • (X.map c)ᵀ) hT
    simpa only [Matrix.map_mul (M := T.1.map c), mm, transpose_mul, h1, Matrix.mul_smul, smul_smul, hε, one_smul,
      Matrix.map_one _ (map_zero c) (map_one c), transpose_one] using this
  have h3 : (two g).1ᵀ * dbl J * (two g).1.map c = dbl G := by
    change (fromBlocks g.1 0 0 g.1)ᵀ * _ * (fromBlocks g.1 0 0 g.1).map c = _
    simp [dbl, fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, hG]
  have h4 : (wit a T).1.map c = fromBlocks 1 ((1 - a) • T.1.map c) 1 (-a • T.1.map c) := by
    have e : c a = 1 - a := by rw [← ha]; ring
    change (fromBlocks 1 (a • T.1) 1 ((a - 1) • T.1)).map c = _
    rw [fromBlocks_map, Matrix.map_one _ (map_zero c) (map_one c)]
    congr 1 <;> ext i j <;> simp [e]
  calc _ = (wit a T).1ᵀ * ((two g).1ᵀ * dbl J * (two g).1.map c) * (wit a T).1.map c := by
        simp only [Units.val_mul, transpose_mul, Matrix.map_mul, Matrix.mul_assoc]
    _ = _ := by
        rw [h3, h4, Matrix.mul_assoc]
        change (fromBlocks 1 (a • T.1) 1 ((a - 1) • T.1))ᵀ * _ = _
        simp only [dbl, fromBlocks_transpose, fromBlocks_multiply, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
          Matrix.neg_mul, Matrix.mul_neg, Matrix.zero_mul, smul_zero, add_zero, zero_add, transpose_smul, transpose_one, hT, h2]
        refine fromBlocks_inj.2 ⟨?_, ?_, ?_, ?_⟩ <;> module

def Int (A : Subring S) {m : Type} (X : Matrix m m S) : Prop := ∀ i j, X i j ∈ A

omit [DecidableEq β] in
theorem Int.mul {A : Subring S} {X Y : Matrix β β S} (h : Int A X) (h' : Int A Y) : Int A (X * Y) :=
  fun _ _ => sum_mem fun _ _ => mul_mem (h _ _) (h' _ _)

theorem int_wit {A : Subring S} {a : S} (ha : a ∈ A) {T : GL β S} (h : Int A T.1) (h' : Int A (T⁻¹).1) :
    Int A (wit a T).1 ∧ Int A ((wit a T)⁻¹).1 := by
  have o : Int A (1 : Matrix β β S) := fun i j => by rw [Matrix.one_apply]; split_ifs; exacts [one_mem _, zero_mem _]
  constructor <;> rintro (i | i) (j | j)
  exacts [o i j, mul_mem ha (h i j), o i j, mul_mem (sub_mem ha (one_mem _)) (h i j),
    mul_mem (sub_mem (one_mem _) ha) (o i j), mul_mem ha (o i j), h' i j, neg_mem (h' i j)]

theorem int_conj {A : Subring S} {a g : GL β S} {l : Sˣ} (hl : a.1 = l.1 • g.1) {w : GL (β ⊕ β) S} (h : Int A w.1)
    (h' : Int A (w⁻¹).1) (x : GL (β ⊕ β) S) :
    Int A ((two a)⁻¹ * x * two a).1 ↔ Int A ((two g * w)⁻¹ * x * (two g * w)).1 := by
  have e : (two a).1 = l.1 • (two g).1 := by
    change fromBlocks _ _ _ _ = l.1 • fromBlocks _ _ _ _
    simp [fromBlocks_smul, hl]
  have e1 : (two a)⁻¹ * x * two a = (two g)⁻¹ * x * two g := by
    have : ∀ y : GL (β ⊕ β) S, two a * ((two g)⁻¹ * y * two g) = y * two a := fun y => Units.ext <| by
      simp only [Units.val_mul, e, Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    rw [mul_assoc, ← this, inv_mul_cancel_left]
  rw [e1]
  refine ⟨fun k => ?_, fun k => ?_⟩
  · rw [show (two g * w)⁻¹ * x * (two g * w) = w⁻¹ * ((two g)⁻¹ * x * two g) * w by group]
    exact (h'.mul k).mul h
  · rw [show (two g)⁻¹ * x * two g = w * ((two g * w)⁻¹ * x * (two g * w)) * w⁻¹ by group]
    exact (h.mul k).mul h'

end Generic

theorem exists_arch {n : ℕ} {J θ : Matrix (Fin n) (Fin n) ℂ} {c : ℂ} (hc : star c * c = 1) (hM : (c • J)ᴴ = c • J) (hd : IsUnit (c • J))
    (h : IsCartan (c • J) θ) : ∃ g : GL (Fin n) ℂ, ∀ T : GL (Fin n) ℂ, g.1ᵀ * J * g.1.map star * T.1.map star = 1 →
      ∀ x : GL (Fin n ⊕ Fin n) ℂ, x.1ᵀ * dbl J * x.1.map star = dbl J →
        (((two g * wit 2⁻¹ T)⁻¹ * x * (two g * wit 2⁻¹ T)).1 * ((two g * wit 2⁻¹ T)⁻¹ * x * (two g * wit 2⁻¹ T)).1ᴴ = 1 ↔
          Commute x.1 (fromBlocks θ 0 0 (-θ))) := by
  obtain ⟨g, ε, s, hs, h1, h2⟩ := Hgt.exists_cartan_frame hM hd h two_ne_zero
  have c0 : c ≠ 0 := right_ne_zero_of_mul_eq_one hc
  refine ⟨g, fun T hT x hx => mul_eq_one_comm.trans (Hgt.unitary_iff_commute (Q := (dbl J)ᵀ) (mul_ne_zero hs c0) ?_ _ x ?_ ?_)⟩
  · have : IsUnit J.det := by
      have := (isUnit_iff_isUnit_det _).1 hd
      rw [det_smul] at this
      exact isUnit_of_mul_isUnit_right this
    rw [isUnit_iff_isUnit_det, det_transpose, dbl, det_fromBlocks_zero₂₁, det_neg]
    exact this.mul ((isUnit_one.neg.pow _).mul this)
  · set D : Matrix (Fin n) (Fin n) ℂ := diagonal fun i => if ε i then 1 else -1 with hD
    have dd : D * D = 1 := by
      rw [hD, diagonal_mul_diagonal, ← diagonal_one]
      congr 1; funext i; split_ifs <;> simp
    have dh : Dᴴ = D := by
      rw [hD, diagonal_conjTranspose]
      congr 1; funext i; simp only [Pi.star_apply]; split_ifs <;> simp
    have e1 : T.1ᴴ * D = (2 * c) • 1 := by
      have := congrArg transpose hT
      rw [transpose_mul, transpose_mul, transpose_mul, transpose_one, transpose_transpose] at this
      rw [← h1, ← this]
      simp only [transpose_smul, smul_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, Complex.ofReal_ofNat]
      rfl
    have e2 : T.1ᴴ = (2 * c) • D := by rw [← Matrix.mul_one T.1ᴴ, ← dd, ← Matrix.mul_assoc, e1, Matrix.smul_mul, Matrix.one_mul]
    have e3 : T.1ᴴ * T.1 = (4 : ℂ) • 1 := by
      have : T.1 = (2 * star c) • D := by rw [← conjTranspose_conjTranspose T.1, e2, conjTranspose_smul, dh]; simp
      rw [e2, this, Matrix.smul_mul, Matrix.mul_smul, dd, smul_smul]
      congr 1
      linear_combination 4 * hc
    have e4 : g.1ᴴ * ((s * c) • (Jᵀ * θ)) * g.1 = (2⁻¹ : ℂ) • 1 := by
      rw [← h2]
      simp only [transpose_smul, smul_smul, Matrix.mul_smul, Matrix.smul_mul, Complex.ofReal_ofNat]
      congr 1
      ring
    have e5 : (two g).1ᴴ * ((s * c) • ((dbl J)ᵀ * fromBlocks θ 0 0 (-θ))) * (two g).1 = (2⁻¹ : ℂ) • 1 := by
      change (fromBlocks g.1 0 0 g.1)ᴴ * _ * fromBlocks g.1 0 0 g.1 = _
      rw [← fromBlocks_one, fromBlocks_smul, ← e4]
      simp [dbl, fromBlocks_transpose, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_smul]
    calc _ = (wit 2⁻¹ T).1ᴴ * ((two g).1ᴴ * ((s * c) • ((dbl J)ᵀ * fromBlocks θ 0 0 (-θ))) * (two g).1) * (wit 2⁻¹ T).1 := by
          simp only [Units.val_mul, conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by
          rw [e5, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
          change _ • ((fromBlocks 1 ((2⁻¹ : ℂ) • T.1) 1 ((2⁻¹ - 1 : ℂ) • T.1))ᴴ * fromBlocks 1 ((2⁻¹ : ℂ) • T.1) 1 ((2⁻¹ - 1 : ℂ) • T.1)) = _
          rw [← fromBlocks_one (l := Fin n) (m := Fin n)]
          simp only [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_smul, conjTranspose_smul, conjTranspose_one, Matrix.mul_one,
            Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, e3, star_sub, star_inv₀, star_ofNat, star_one]
          refine fromBlocks_inj.2 ⟨?_, ?_, ?_, ?_⟩ <;> module
  · have := congrArg transpose hx
    rw [transpose_mul, transpose_mul, transpose_transpose, ← Matrix.mul_assoc] at this
    exact this

end GlobalTheory.ThK.Dbl.Frame

end
end

section

noncomputable section

namespace GlobalTheory.ThK.Dbl.Inert

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.LFun.InertChart PositivityTheory.ThK PositivityTheory.ThKH.Iwas PositivityTheory.ThKH.Locpair PositivityTheory.ThKH.Locrep
open GlobalTheory.EmbChart (atPlace evFin_atPlace atPlace_mul_right tensAt)
open GlobalTheory.Doubling (absE)

section Alg

variable {L : Type} [CommRing L] {β γ : Type} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]

def conjM {A : Matrix β γ L} {A' : Matrix γ β L} (h1 : A * A' = 1) (h2 : A' * A = 1) : Matrix γ γ L →* Matrix β β L where
  toFun m := A * m * A'
  map_one' := by rw [Matrix.mul_one, h1]
  map_mul' a b := by
    rw [show A * a * A' * (A * b * A') = A * (a * (A' * A) * b) * A' by simp only [Matrix.mul_assoc], h2, Matrix.mul_one]

theorem iso_iff (c : L →+* L) {A : Matrix β γ L} {A' : Matrix γ β L} (h1 : A * A' = 1) {J : Matrix β β L} {H : Matrix γ γ L}
    (hH : cT c A * Jᵀ * A = H) (M : Matrix β β L) :
    Mᵀ * J * M.map c = J ↔ cT c (A' * M * A) * H * (A' * M * A) = H := by
  have e : cT c (A' * M * A) * H * (A' * M * A) = cT c A * (Mᵀ * J * M.map c)ᵀ * A := by
    have : A * (A' * M * A) = M * A := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul]
    calc _ = cT c (A * (A' * M * A)) * Jᵀ * (A * (A' * M * A)) := by rw [← hH, cT_mul c A]; simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [this, cT_mul]
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc, cT]
  have k : ∀ X : Matrix β β L, cT c A' * (cT c A * X * A) * A' = X := fun X => by
    calc _ = cT c (A * A') * X * (A * A') := by rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, cT_one, Matrix.one_mul, Matrix.mul_one]
  rw [e, ← hH]
  exact ⟨fun h => by rw [h], fun h => Matrix.transpose_injective ((k _).symm.trans ((congrArg (cT c A' * · * A') h).trans (k _)))⟩

end Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {v : Pl F} {w : HeightOneSpectrum (𝓞 E)} {Y : Spc F E n}

omit [NumberField E] in
theorem latW_le : latW Y v ≤ latHat Y := AddSubgroup.closure_mono (by
  rintro _ ⟨a, ha, hi, x, hx, rfl⟩
  have e : a = atPlace v (evFin F v a) := by simpa [atPlace_mul_right] using (idem_smul ha).symm
  refine ⟨a, by rw [e]; exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F), fun u => ?_, x, hx, rfl⟩
  by_cases hu : u = v
  · exact hu ▸ hi
  · rw [e, show evFin F u (atPlace v (evFin F v a)) = 0 from evalV_singleFin_ne hu _]; exact zero_mem _)

omit [NumberField E] in
theorem idem_mem {z : Fin n → AE F E} (hz : z ∈ latHat Y) : atPlace v (1 : Fv F v) • z ∈ latW Y v := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, -, hi, x, hx, rfl⟩ := hz
    exact AddSubgroup.subset_closure ⟨atPlace v 1 • a, at_smul_idem v a, by
      rw [smul_eq_mul, map_mul, evFin_atPlace, one_mul]; exact hi v, x, hx, by rw [smul_smul]; rfl⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | neg a _ ha => rw [smul_neg]; exact neg_mem ha

omit [NumberField E] in
theorem stab_latW {g : Matrix (Fin n) (Fin n) (AE F E)} (hat : ∀ z ∈ latW Y v, At (evFin F v) z) :
    (∀ z ∈ latHat Y, At (evFin F v) z → g *ᵥ z ∈ latHat Y) ↔ ∀ z ∈ latW Y v, g *ᵥ z ∈ latW Y v :=
  ⟨fun h z hz => idem_smul (at_mulVec_right g (hat z hz)) ▸ idem_mem (h z (latW_le hz) (hat z hz)),
    fun h z hz ha => latW_le (h z (idem_smul ha ▸ idem_mem hz))⟩

omit [NumberField E] in
theorem mulVec_latHat {N : Matrix (Fin n) (Fin n) (AE F E)} (hN : At (evFin F v) N) (h : ∀ z ∈ latW Y v, N *ᵥ z ∈ latW Y v)
    {z : Fin n → AE F E} (hz : z ∈ latHat Y) : N *ᵥ z ∈ latHat Y := by
  have := latW_le (h _ (idem_mem hz))
  rwa [Matrix.mulVec_smul, idem_smul (at_mulVec_left hN z)] at this

omit [NumberField E] in
theorem piInf_at {u : InfinitePlace F} (τ : EmbOver E u) {z : AE F E} (hz : At (evFin F v) z) : piInf τ z = 0 := by
  have h0 : compInf F E u (algebraMap (AF F) (AE F E) (atPlace v 1)) = 0 :=
    (congrArg (· ⊗ₜ[F] _) (show evInf F u (atPlace v 1) = 0 from rfl)).trans (TensorProduct.zero_tmul _ _)
  rw [← idem_smul hz, Algebra.smul_def, piInf, RingHom.comp_apply, map_mul, h0, zero_mul, map_zero]

theorem mem_K {B : Base F E} {K : Subgroup (G2 σ Y)} (hK : IsStab2 B K) {k : G2 σ Y}
    (h : ∀ x ∈ ({k, k⁻¹} : Set (G2 σ Y)), At (evFin F v) (mat2 x - 1) ∧ ∀ i j : Fin n → Fin n ⊕ Fin n, i ∈ ({.inl, .inr} : Set _) →
      j ∈ ({.inl, .inr} : Set _) → ∀ z ∈ latW Y v, (mat2 x - 1).submatrix i j *ᵥ z ∈ latW Y v) : k ∈ K := by
  refine (hK k).2 ⟨fun u => ?_, fun z z' hz hz' x hx => ?_⟩
  · have : (mat2 k).map (piInf (B.emb u)) = 1 := Matrix.ext fun i j => by
      have := piInf_at (B.emb u) (z := (mat2 k - 1) i j) fun a ha => congrFun (congrFun ((h k (by simp)).1 a ha) i) j
      rw [Matrix.sub_apply, map_sub, sub_eq_zero] at this
      simpa [Matrix.one_apply, apply_ite] using this
    rw [this]; exact Commute.one_left _
  · obtain ⟨h1, h2⟩ := h x hx
    have key : ∀ i : Fin n → Fin n ⊕ Fin n, i ∈ ({.inl, .inr} : Set _) → Sum.elim z z' ∘ i ∈ latHat Y →
        (mat2 x *ᵥ Sum.elim z z') ∘ i ∈ latHat Y := fun i hi h3 => by
      have b : ∀ j : Fin n → Fin n ⊕ Fin n, At (evFin F v) ((mat2 x - 1).submatrix i j) := fun j a ha =>
        Matrix.ext fun _ _ => congrFun (congrFun (h1 a ha) _) _
      convert add_mem h3 (add_mem (mulVec_latHat (b .inl) (h2 i _ hi (by simp)) hz) (mulVec_latHat (b .inr) (h2 i _ hi (by simp)) hz'))
      have : mat2 x *ᵥ Sum.elim z z' = Sum.elim z z' + (mat2 x - 1) *ᵥ Sum.elim z z' := by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, add_sub_cancel]
      rw [this]
      ext l
      simp [Matrix.mulVec, dotProduct]
    exact ⟨key _ (by simp) hz, key _ (by simp) hz'⟩

variable (hw : IsInertAt F E v w) (h : w.under (𝓞 F) = v) {β γ : Type} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]


variable (β) in
def up : Matrix β β (w.adicCompletion E) →* Matrix β β (AE F E) :=
  (liftM E v β).comp (RingHom.mapMatrix (complEquiv hw h).symm.toRingHom).toMonoidHom

theorem up_pi (m : Matrix β β (w.adicCompletion E)) : (up hw h β m).map (piE h) = m := Matrix.ext fun i j =>
  (congrArg (toCompl h) (congrFun (congrFun (comp_liftM v _) i) j)).trans ((complEquiv hw h).apply_symm_apply _)

theorem up_aw (m : Matrix β β (w.adicCompletion E)) : (up hw h β m).map (aw E v) = 1 := aw_liftM v _

theorem up_at (m : Matrix β β (w.adicCompletion E)) : At (evFin F v) (up hw h β m - 1) := at_liftM v _

include hw in
theorem extW {ι κ : Type} {a b : Matrix ι κ (AE F E)} (h1 : a.map (piE h) = b.map (piE h)) (h2 : a.map (aw E v) = b.map (aw E v)) :
    a = b := extM v (Matrix.ext fun i j => (toCompl_bijective hw h).1 (congrFun (congrFun h1 i) j)) h2

theorem continuous_tensAt : Continuous (tensAt E v : Ev E v → AE F E) := by
  haveI : IsModuleTopology (Fv F v) (Ev E v) := ⟨rfl⟩
  haveI : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) _
  let b := Algebra.TensorProduct.basis (Fv F v) (Module.finBasis F E)
  have e : (tensAt E v : Ev E v → AE F E) = fun y => ∑ i, atPlace v (b.coord i y) • tensAt E v (b i) := by
    funext y

    conv_lhs => rw [← b.sum_repr y, map_sum]
    exact Finset.sum_congr rfl fun i _ => smul_tensAt v _ _
  rw [e]
  exact continuous_finsetSum _ fun i _ => ((GlobalTheory.VacAny.continuous_atPlace v).comp
    (IsModuleTopology.continuous_of_linearMap (b.coord i))).smul continuous_const

theorem continuous_up : Continuous (up hw h β) := by
  haveI : IsModuleTopology (Fv F v) (Ev E v) := ⟨rfl⟩
  haveI : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) _
  haveI : IsTopologicalAddGroup (Ev E v) := IsModuleTopology.topologicalAddGroup (Fv F v) _
  have c1 : Continuous (liftM E v β) :=
    continuous_const.add ((continuous_id.sub continuous_const).matrix_map continuous_tensAt)
  exact c1.comp (continuous_id.matrix_map (continuous_complEquiv hw h).2)

include hw in
theorem continuous_piE : Continuous (piE h) := (continuous_complEquiv hw h).1.comp
  (GlobalTheory.AutFunCompare.continuous_tensNU (E := E) (evFin F v).toLinearMap (map_mul (evFin F v))
    ((RestrictedProduct.continuous_eval v).comp continuous_snd))

variable {h} {c : w.adicCompletion E →+* w.adicCompletion E} (hc : IsConjAt σ h c) {J : Matrix β β (AE F E)}
  {A : Matrix β γ (w.adicCompletion E)} {A' : Matrix γ β (w.adicCompletion E)} (h1 : A * A' = 1) (h2 : A' * A = 1)
  {H : Matrix γ γ (w.adicCompletion E)} (hH : cT c A * (J.map (piE h))ᵀ * A = H)

omit [DecidableEq β] in
include hc in
theorem pi_gram (M : Matrix β β (AE F E)) :
    (Mᵀ * J * M.map (cA σ)).map (piE h) = (M.map (piE h))ᵀ * J.map (piE h) * (M.map (piE h)).map c := by
  rw [Matrix.map_mul, Matrix.map_mul]
  exact congrArg _ (Matrix.ext fun i j => piE_cA hc _)

def liftW : UJ c H →* UG (cA σ) J :=
  ((Units.map ((up hw h β).comp (conjM h1 h2))).comp (UJ c H).subtype).codRestrict _ fun g => by
    change (up hw h β (A * g.1.1 * A'))ᵀ * J * (up hw h β (A * g.1.1 * A')).map (cA σ) = J
    refine extW hw h ?_ ?_
    · rw [pi_gram hc, up_pi, iso_iff c h1 hH, show A' * (A * g.1.1 * A') * A = A' * A * g.1.1 * (A' * A) by
        simp only [Matrix.mul_assoc], h2, Matrix.one_mul, Matrix.mul_one]
      exact g.2
    · rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, awM_cA, up_aw, Matrix.transpose_one,
        Matrix.map_one _ (map_zero _) (map_one _), one_mul, mul_one]

def downW : UG (cA σ) J →* UJ c H :=
  ((Units.map ((conjM h2 h1).comp (piE h).mapMatrix.toMonoidHom)).comp (UG (cA σ) J).subtype).codRestrict _ fun g =>
    (iso_iff c h1 hH _).1 ((pi_gram hc g.1.1).symm.trans (congrArg (·.map (piE h)) g.2))

theorem continuous_liftW : Continuous (liftW hw hc h1 h2 hH) :=
  ((Units.continuous_map ((continuous_up hw h).comp ((continuous_const.matrix_mul continuous_id).matrix_mul
    continuous_const))).comp continuous_subtype_val).subtype_mk _

include hw in
theorem continuous_downW : Continuous (downW hc h1 h2 hH) :=
  ((Units.continuous_map ((continuous_const.matrix_mul (continuous_id.matrix_map (continuous_piE hw h))).matrix_mul
    continuous_const)).comp continuous_subtype_val).subtype_mk _

theorem down_lift (x : UJ c H) : downW hc h1 h2 hH (liftW hw hc h1 h2 hH x) = x := Subtype.ext (Units.ext (by
  change A' * (up hw h β (A * x.1.1 * A')).map (piE h) * A = x.1.1
  rw [up_pi, show A' * (A * x.1.1 * A') * A = A' * A * x.1.1 * (A' * A) by simp only [Matrix.mul_assoc], h2, Matrix.one_mul,
    Matrix.mul_one]))

theorem lift_down {g : UG (cA σ) J} (hg : At (evFin F v) (g.1.1 - 1)) : liftW hw hc h1 h2 hH (downW hc h1 h2 hH g) = g :=
  Subtype.ext (Units.ext (mat_inj hw h (sub_sub_sub_cancel_right _ _ (1 : Matrix β β (AE F E)) ▸ at_sub (up_at hw h _) hg) (by
    refine (up_pi hw h _).trans ?_
    change A * (A' * g.1.1.map (piE h) * A) * A' = _
    rw [show ∀ M, A * (A' * M * A) * A' = A * A' * M * (A * A') from fun M => by simp only [Matrix.mul_assoc], h1, Matrix.one_mul,
      Matrix.mul_one])))

end GlobalTheory.ThK.Dbl.Inert

end
end

section

noncomputable section

namespace GlobalTheory.ThK.Dbl.TC

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem splitModel_of (h : PositivityTheory.KCo.DictX) : SplitModel := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' p v t
  obtain ⟨⟨ι, hι⟩, -, s2, k⟩ := h F E σ n d B X W M om χX χW p.base ⟨_, _, p.herm⟩ ⟨_, _, p.skew⟩ p.weil v t
  exact ⟨s2, ι, hι.bij, fun g hg => ⟨Matrix.GeneralLinearGroup.map (piW t) g.1, (k ι hι).1 g hg _ rfl⟩, (k ι hι).2⟩

theorem splitModel : SplitModel := splitModel_of PositivityTheory.KCo.dictionary_extended

end GlobalTheory.ThK.Dbl.TC

end
end
