module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1197
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
import Mathlib.RingTheory.PiTensorProduct
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

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.DblVac

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev UD (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) : Type := UG (cA σ) (dbl (incM F W.J))

def matD {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} (g : UD σ W) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) := g.1.1

def latD {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) : Set (Fin d ⊕ Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
  {z | z ∘ Sum.inl ∈ GlobalTheory.InertSph.latAt W v ∧ z ∘ Sum.inr ∈ GlobalTheory.InertSph.latAt W v}

def KD (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) : Set (UD σ W) :=
  {g | At (evFin F v) (matD g - 1) ∧ ∀ z ∈ latD W v, matD g *ᵥ z ∈ latD W v ∧ matD g⁻¹ *ᵥ z ∈ latD W v}

def PDiag (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) : Set (UD σ W) :=
  {p | ∃ t : GL (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), matD p * diagCols (Fin d) = diagCols (Fin d) * (t : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))}

def antiCols (d : ℕ) : Matrix (Fin d ⊕ Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) := Matrix.fromRows 1 (-1)

def PAnti (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) : Set (UD σ W) :=
  {p | ∃ t : GL (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), matD p * antiCols d = antiCols d * (t : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))}

end GlobalTheory.DblVac
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.InertSph

theorem evFin_invTwo_mem {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) :
    evFin F v (⅟(2 : AF F)) ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have hv2 : Valued.v (2 : Fv F v) = 1 := by
    have e := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v (2 : 𝓞 F)
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.2 h2] at e
    rw [← e]; congr 1; exact (map_ofNat (algebraMap (𝓞 F) (Fv F v)) 2).symm
  have hm : evFin F v (⅟(2 : AF F)) * 2 = 1 := by
    rw [← map_ofNat (evFin F v) 2, ← map_mul, invOf_mul_self, map_one]
  have hvm := congrArg Valued.v hm
  rw [map_mul, hv2, mul_one, map_one] at hvm
  exact hvm.le

theorem invTwo_smul_mem_latAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (W : Spc F E d)
    (v : Pl (F := F)), (2 : 𝓞 F) ∉ v.asIdeal → ∀ z ∈ GlobalTheory.InertSph.latAt W v, (⅟(2 : AF F)) • z ∈ GlobalTheory.InertSph.latAt W v := by
  intro F E _ _ _ _ _ d W v h2 z hz
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hv, y, hy, rfl⟩ := hz
    rw [smul_smul]
    refine AddSubgroup.subset_closure ⟨⅟(2 : AF F) * a, ?_, ?_, y, hy, rfl⟩
    · intro u hu
      rw [smul_eq_mul, mul_left_comm, ← smul_eq_mul u a, ha u hu, mul_zero]
    · rw [map_mul]
      exact mul_mem (evFin_invTwo_mem v h2) hv
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

end GlobalTheory.InertSph
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.InertBridge

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def Chart (σ : E →ₐ[F] E) (B : Base F E) {a a' : ℕ} (G : Geo σ a a') (v : Pl (F := F)) {L : Type} [Field L]
    [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σL : L →+* L) (q : ℕ) (δ : L) (JS : GL (Fin a') L)
    (JT : GL (Fin (a + a')) L) (ψL : AddChar L ℂ)
    (κ : Matrix (Fin (a + a')) (Fin a') L →+ Matrix (Fin a') (Fin (a + a')) (AE F E))
    (ιS : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) →* UA σ G.V'.J)
    (ιT : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →* UA σ G.W.J) : Prop :=
  Formalism.UG.IsUnramInv ϖ σL q ∧ Odd q ∧
  JS ∈ Formalism.UG.GLint (Fin a') (Formalism.UG.intL L) ∧ JT ∈ Formalism.UG.GLint (Fin (a + a')) (Formalism.UG.intL L) ∧
  (∀ i j, σL ((JS : Matrix (Fin a') (Fin a') L) i j) = (JS : Matrix (Fin a') (Fin a') L) j i) ∧
  (∀ i j, σL ((JT : Matrix (Fin (a + a')) (Fin (a + a')) L) i j) = (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) j i) ∧
  (Valued.v δ = 1 ∧ σL δ = -δ) ∧
  (∀ z ∈ Formalism.UG.intL L, σL z = z → ψL z = 1) ∧
  (∃ z ∈ Formalism.UG.intL L, σL z = z ∧ ψL (ϖ⁻¹ * z) ≠ 1) ∧
  (∀ x, At (evFin F v) (κ x)) ∧
  (∀ γ : Matrix (Fin a') (Fin (a + a')) (AE F E), At (evFin F v) γ → ∃ x, κ x = γ) ∧
  (∀ x, (∀ i j, x i j ∈ Formalism.UG.intL L) ↔ κ x ∈ latAtV G.V' G.W v) ∧
  (∀ x y, ψL ((GlobalTheory.Hk3.locH σL δ JS JT x y + σL (GlobalTheory.Hk3.locH σL δ JS JT x y)) / 2) =
    B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (κ x) (κ y))) ∧
  (∀ g h x, actAB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (ιS g, ιT h) (κ x) =
    κ (((h : GL (Fin (a + a')) L) : Matrix (Fin (a + a')) (Fin (a + a')) L) * x *
      (((g : GL (Fin a') L)⁻¹ : GL (Fin a') L) : Matrix (Fin a') (Fin a') L))) ∧
  (∀ g, ιS g ∈ UAt σ G.V' (evFin F v)) ∧ (∀ h, ιT h ∈ UAt σ G.W (evFin F v)) ∧
  (∀ g : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L),
    (g : GL (Fin a') L) ∈ Formalism.UG.GLint (Fin a') (Formalism.UG.intL L) → ιS g ∈ GlobalTheory.InertSph.KAt σ G.V' v) ∧
  (∀ h : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L),
    (h : GL (Fin (a + a')) L) ∈ Formalism.UG.GLint (Fin (a + a')) (Formalism.UG.intL L) → ιT h ∈ GlobalTheory.InertSph.KAt σ G.W v)

end GlobalTheory.InertBridge

end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertLocFrame.Lat

theorem mem_of_bil {A B C : Type} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] (g : A →+ B →+ C)
    {SA : Set A} {SB : Set B} {T : AddSubgroup C} (h : ∀ a ∈ SA, ∀ b ∈ SB, g a b ∈ T) {a : A} {b : B}
    (ha : a ∈ AddSubgroup.closure SA) (hb : b ∈ AddSubgroup.closure SB) : g a b ∈ T := by
  induction ha using AddSubgroup.closure_induction with
  | mem a ha =>
    induction hb using AddSubgroup.closure_induction with
    | mem b hb => exact h a ha b hb
    | zero => simpa using T.zero_mem
    | add b b' _ _ h1 h2 => simpa using T.add_mem h1 h2
    | neg b _ h1 => simpa using T.neg_mem h1
  | zero => simpa using T.zero_mem
  | add a a' _ _ h1 h2 => simpa using T.add_mem h1 h2
  | neg a _ h1 => simpa using T.neg_mem h1

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def intAt (v : Pl (F := F)) : AddSubgroup (AE F E) :=
  AddSubgroup.closure {z : AE F E | ∃ a : AF F, At (evFin F v) a ∧
    evFin F v a ∈ v.adicCompletionIntegers F ∧ ∃ o : 𝓞 E, z = a • inclR (F := F) (AF F) (o : E)}

theorem at_mul {v : Pl (F := F)} {a : AF F} (b : AF F) (ha : At (evFin F v) a) : At (evFin F v) (a * b) := by
  intro u hu
  have h := ha u hu
  rw [smul_eq_mul] at h ⊢
  rw [← mul_assoc, h, zero_mul]

theorem int_mul {v : Pl (F := F)} {a b : AF F} (ha : evFin F v a ∈ v.adicCompletionIntegers F)
    (hb : evFin F v b ∈ v.adicCompletionIntegers F) : evFin F v (a * b) ∈ v.adicCompletionIntegers F := by
  rw [map_mul]
  exact mul_mem ha hb

def smulHom (n : ℕ) : AE F E →+ (Fin n → AE F E) →+ (Fin n → AE F E) :=
  AddMonoidHom.mk' (fun c => DistribSMul.toAddMonoidHom _ c)
    (fun c c' => AddMonoidHom.ext fun x => by funext i; simp [add_mul])

theorem smul_mem_latAt {v : Pl (F := F)} {n : ℕ} (X : Spc F E n) {c : AE F E} (hc : c ∈ intAt v) {x : Fin n → AE F E}
    (hx : x ∈ GlobalTheory.InertSph.latAt X v) : c • x ∈ GlobalTheory.InertSph.latAt X v := by
  refine mem_of_bil (smulHom n) ?_ hc hx
  rintro _ ⟨b, hb, hbi, o, rfl⟩ _ ⟨a, ha, hai, y, hy, rfl⟩
  refine AddSubgroup.subset_closure ⟨b * a, at_mul a hb, int_mul hbi hai, o • y, X.L.smul_mem o hy, ?_⟩
  funext i
  have ho : algebraMap (𝓞 E) E o = (o : E) := rfl
  simp only [smulHom, AddMonoidHom.mk'_apply, DistribSMul.toAddMonoidHom_apply, Pi.smul_apply, smul_eq_mul]
  simp only [Algebra.smul_def, map_mul, ho]
  ring

theorem smul_incl_mem_latAt {v : Pl (F := F)} {n : ℕ} (X : Spc F E n) {c : AE F E} (hc : c ∈ intAt v) {y : Fin n → E}
    (hy : y ∈ X.L) : (c • fun i => inclR (F := F) (AF F) (y i)) ∈ GlobalTheory.InertSph.latAt X v := by
  refine mem_of_bil (smulHom n) (SB := {fun i => inclR (F := F) (AF F) (y i)}) ?_ hc (AddSubgroup.subset_closure rfl)
  rintro _ ⟨b, hb, hbi, o, rfl⟩ _ rfl
  refine AddSubgroup.subset_closure ⟨b, hb, hbi, o • y, X.L.smul_mem o hy, ?_⟩
  funext i
  have ho : algebraMap (𝓞 E) E o = (o : E) := rfl
  simp only [smulHom, AddMonoidHom.mk'_apply, DistribSMul.toAddMonoidHom_apply, Pi.smul_apply, smul_eq_mul]
  simp only [Algebra.smul_def, map_mul, ho]
  ring

theorem vecMulVec_mem {v : Pl (F := F)} {n d : ℕ} (X : Spc F E n) (W : Spc F E d) {x : Fin n → AE F E} {y : Fin d → AE F E}
    (hx : x ∈ GlobalTheory.InertSph.latAt X v) (hy : y ∈ GlobalTheory.InertSph.latAt W v) : Matrix.vecMulVec x y ∈ latAtV X W v := by
  let g : (Fin n → AE F E) →+ (Fin d → AE F E) →+ Matrix (Fin n) (Fin d) (AE F E) :=
    AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun y => Matrix.vecMulVec x y)
        (fun y y' => by ext i j; simp [Matrix.vecMulVec_apply, mul_add]))
      (fun x x' => AddMonoidHom.ext fun y => by ext i j; simp [Matrix.vecMulVec_apply, add_mul])
  refine mem_of_bil g ?_ hx hy
  rintro _ ⟨a, ha, hai, x0, hx0, rfl⟩ _ ⟨b, hb, hbi, y0, hy0, rfl⟩
  refine AddSubgroup.subset_closure ⟨a * b, at_mul b ha, int_mul hai hbi, x0, hx0, y0, hy0, ?_⟩
  ext i j
  simp only [g, AddMonoidHom.mk'_apply, Matrix.vecMulVec_apply, incM, Matrix.smul_apply, Matrix.map_apply, Pi.smul_apply,
    smul_eq_mul]
  simp only [Algebra.smul_def, map_mul]
  ring

end GlobalTheory.InertLocFrame.Lat

namespace GlobalTheory.InertLocFrame


open GlobalTheory.InertLocFrame.Lat in
theorem mem_latAtV_iff_xm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl (F := F)) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ι : L →+ AE F E),
      Function.Injective ι → (∀ z : AE F E, At (evFin F v) z ↔ ∃ x, ι x = z) → (∀ x y, ι (x * y) = ι x * ι y) →
      (∀ x, x ∈ Formalism.UG.intL L ↔ ι x ∈ AddSubgroup.closure {z : AE F E | ∃ a : AF F, At (evFin F v) a ∧
        evFin F v a ∈ v.adicCompletionIntegers F ∧ ∃ o : 𝓞 E, z = a • inclR (F := F) (AF F) (o : E)}) →
      ∀ (PV : GL (Fin n) L) (PW : GL (Fin d) L), (∀ x : Fin n → L, (∀ i, x i ∈ Formalism.UG.intL L) ↔
        (fun i => ι (((PV : Matrix (Fin n) (Fin n) L) *ᵥ x) i)) ∈ GlobalTheory.InertSph.latAt X v) → (∀ x : Fin d → L, (∀ i, x i ∈ Formalism.UG.intL L) ↔
        (fun i => ι (((PW : Matrix (Fin d) (Fin d) L) *ᵥ x) i)) ∈ GlobalTheory.InertSph.latAt W v) →
      ∀ z, z ∈ latAtV X W v ↔ ∃ u : Matrix (Fin d) (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) ∧
        GlobalTheory.InertLocFrame.xm ι PV PW u = z := by
  intro F E _ _ _ _ _ v n d X W L _ _ ι hinj hsupp hmul hint PV PW hPV hPW z
  have hsing : ∀ {m : ℕ} (j i : Fin m), (Pi.single j (1 : L) : Fin m → L) i ∈ Formalism.UG.intL L := by
    intro m j i
    rw [Pi.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  constructor
  · intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, hai, x, hx, y, hy, rfl⟩ := hz
      have h1 : ι 1 ∈ Lat.intAt (E := E) v := (hint 1).1 (one_mem _)
      have h1s : At (evFin F v) (ι 1) := (hsupp _).2 ⟨1, rfl⟩
      let X' : Fin n → AE F E := a • fun i => inclR (F := F) (AF F) (x i)
      let Y' : Fin d → AE F E := ι 1 • fun k => inclR (F := F) (AF F) (y k)
      have hX'm : X' ∈ GlobalTheory.InertSph.latAt X v := AddSubgroup.subset_closure ⟨a, ha, hai, x, hx, rfl⟩
      have hY'm : Y' ∈ GlobalTheory.InertSph.latAt W v := Lat.smul_incl_mem_latAt W h1 hy
      have hX's : ∀ i, ∃ t, ι t = X' i := fun i => (hsupp _).1 fun u hu => by
        show u • (a • inclR (F := F) (AF F) (x i)) = 0
        rw [smul_smul, ← smul_eq_mul, ha u hu, zero_smul]
      have hY's : ∀ k, ∃ t, ι t = Y' k := fun k => (hsupp _).1 fun u hu => by
        show u • (ι 1 * inclR (F := F) (AF F) (y k)) = 0
        rw [← smul_mul_assoc, h1s u hu, zero_mul]
      let xt : Fin n → L := fun i => pre ι (X' i)
      let yt : Fin d → L := fun k => pre ι (Y' k)
      have hxt : ∀ i, ι (xt i) = X' i := fun i => pre_spec ι (hX's i)
      have hyt : ∀ k, ι (yt k) = Y' k := fun k => pre_spec ι (hY's k)
      let c : Fin n → L := ((PV⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ xt
      let c' : Fin d → L := ((PW⁻¹ : GL (Fin d) L) : Matrix (Fin d) (Fin d) L) *ᵥ yt
      have hPc : (PV : Matrix (Fin n) (Fin n) L) *ᵥ c = xt := by
        simp only [c]
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
      have hPc' : (PW : Matrix (Fin d) (Fin d) L) *ᵥ c' = yt := by
        simp only [c']
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
      have hc : ∀ i, c i ∈ Formalism.UG.intL L := (hPV c).2 (by
        rw [hPc]
        convert hX'm using 1
        funext i
        exact hxt i)
      have hc' : ∀ k, c' k ∈ Formalism.UG.intL L := (hPW c').2 (by
        rw [hPc']
        convert hY'm using 1
        funext k
        exact hyt k)
      refine ⟨Matrix.vecMulVec c' c, fun i j => mul_mem (hc' i) (hc j), ?_⟩
      ext i k
      rw [xm_apply, Matrix.map_apply]
      have e1 : ((PV : Matrix (Fin n) (Fin n) L) * (Matrix.vecMulVec c' c)ᵀ * (PW : Matrix (Fin d) (Fin d) L)ᵀ) i k = xt i * yt k := by
        rw [← hPc, ← hPc']
        simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct,
          Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
      have e2 : ι 1 * X' i = X' i := by rw [← hxt i, ← hmul, one_mul]
      rw [e1, hmul, hxt, hyt]
      show X' i * (ι 1 * inclR (F := F) (AF F) (y k)) = (a • incM F (Matrix.vecMulVec x y)) i k
      rw [← mul_assoc, mul_comm (X' i), e2]
      simp only [X', incM, Matrix.smul_apply, Matrix.map_apply, Matrix.vecMulVec_apply, Pi.smul_apply, map_mul,
        smul_mul_assoc]
    | zero => exact ⟨0, fun _ _ => zero_mem _, map_zero _⟩
    | add z z' _ _ h h' =>
      obtain ⟨u, hu, rfl⟩ := h
      obtain ⟨u', hu', rfl⟩ := h'
      exact ⟨u + u', fun i j => add_mem (hu i j) (hu' i j), map_add _ _ _⟩
    | neg z _ h =>
      obtain ⟨u, hu, rfl⟩ := h
      exact ⟨-u, fun i j => neg_mem (hu i j), map_neg _ _⟩
  · rintro ⟨u, hu, rfl⟩
    have e : xm ι PV PW u = ∑ j, ∑ l, Matrix.vecMulVec (ι (u l j) • fun i => ι ((PV : Matrix _ _ L) i j))
        (fun k => ι ((PW : Matrix _ _ L) k l)) := by
      ext i k

      simp only [xm_apply, Matrix.map_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.sum_apply,
      Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, map_sum, hmul]
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [e]
    refine sum_mem fun j _ => sum_mem fun l _ => Lat.vecMulVec_mem X W (Lat.smul_mem_latAt X ((hint _).1 (hu l j)) ?_) ?_
    · have h := (hPV (Pi.single j 1)).1 (hsing j)
      simpa [Matrix.mulVec_single_one] using h
    · have h := (hPW (Pi.single l 1)).1 (hsing l)
      simpa [Matrix.mulVec_single_one] using h

end GlobalTheory.InertLocFrame

end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertKatFrame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem latAt_entry_at {n : ℕ} (X : Spc F E n) (v : Pl (F := F)) {z : Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)}
    (hz : z ∈ GlobalTheory.InertSph.latAt X v) (i : Fin n) : At (evFin F v) (z i) := by
  induction hz using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, -, y, -, rfl⟩ := hx
    intro u hu
    have h0 := ha u hu
    rw [smul_eq_mul] at h0
    simp only [Pi.smul_apply]
    rw [smul_smul, h0, zero_smul]
  | zero => intro u _; simp
  | add x y _ _ hx hy => intro u hu; simp [smul_add, hx u hu, hy u hu]
  | neg x _ hx => intro u hu; simp [smul_neg, hx u hu]

theorem mulVec_mem_latAt {n : ℕ} (X : Spc F E n) (v : Pl (F := F)) {L : Type} [Field L]
    [Valued L (WithZero (Multiplicative ℤ))] (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))
    (hsurj : ∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ↔ ∃ x, ι x = z) (hmul : ∀ x y, ι (x * y) = ι x * ι y)
    (P : GL (Fin n) L) (hP : ∀ x : Fin n → L, (∀ i, x i ∈ Formalism.UG.intL L) ↔
        (fun i => ι (((P : Matrix (Fin n) (Fin n) L) *ᵥ x) i)) ∈ GlobalTheory.InertSph.latAt X v)
    (K : Matrix (Fin n) (Fin n) L) (hK : ∀ i j, K i j ∈ Formalism.UG.intL L)
    (A : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (hA : A = (1 - ι 1) • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) +
          ((P : Matrix (Fin n) (Fin n) L) * K * ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)).map ι)
    (z : Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (hz : z ∈ GlobalTheory.InertSph.latAt X v) : A *ᵥ z ∈ GlobalTheory.InertSph.latAt X v := by
  obtain ⟨y, rfl⟩ : ∃ y : Fin n → L, z = fun i => ι (y i) :=
    ⟨fun i => GlobalTheory.InertLocFrame.pre ι (z i), funext fun i =>
      (GlobalTheory.InertLocFrame.pre_spec ι ((hsurj _).1 (latAt_entry_at X v hz i))).symm⟩
  obtain ⟨x, rfl⟩ : ∃ x : Fin n → L, y = (P : Matrix (Fin n) (Fin n) L) *ᵥ x := by
    refine ⟨((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ y, ?_⟩
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have hx := (hP x).2 hz
  have hKx : ∀ i, (K *ᵥ x) i ∈ Formalism.UG.intL L := fun i => by
    simp only [Matrix.mulVec, dotProduct]
    exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hK i j) (hx j)
  have key : A *ᵥ (fun i => ι (((P : Matrix (Fin n) (Fin n) L) *ᵥ x) i)) =
      fun i => ι (((P : Matrix (Fin n) (Fin n) L) *ᵥ (K *ᵥ x)) i) := by
    set N := (P : Matrix (Fin n) (Fin n) L) * K * ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hN
    set Y := (P : Matrix (Fin n) (Fin n) L) *ᵥ x with hY
    have h1 : (1 - ι 1) • (fun i => ι (Y i)) = 0 := by
      funext j
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [sub_mul, one_mul, ← hmul, one_mul, sub_self]
    have h2 : N.map ι *ᵥ (fun i => ι (Y i)) = fun i => ι ((N *ᵥ Y) i) := by
      funext i
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]

      rw [map_sum]
      simp_rw [hmul]
    have h3 : N *ᵥ Y = (P : Matrix (Fin n) (Fin n) L) *ᵥ (K *ᵥ x) := by
      rw [hY, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hN, Matrix.mul_assoc, ← Units.val_mul,
        inv_mul_cancel, Units.val_one, Matrix.mul_one]
    rw [hA, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, h1, zero_add, h2, h3]
  rw [key]
  exact (hP _).1 hKx

theorem mem_KAt_of_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (v : Pl (F := F)) (n : ℕ) (X : Spc F E n) (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      Function.Injective ι → (∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ↔ ∃ x, ι x = z) → (∀ x y, ι (x * y) = ι x * ι y) →
      (∀ x, x ∈ Formalism.UG.intL L ↔ ι x ∈ AddSubgroup.closure {z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) | ∃ a : AF F, At (evFin F v) a ∧
        evFin F v a ∈ v.adicCompletionIntegers F ∧ ∃ o : 𝓞 E, z = a • inclR (F := F) (AF F) (o : E)}) →
      ∀ P : GL (Fin n) L, (∀ x : Fin n → L, (∀ i, x i ∈ Formalism.UG.intL L) ↔
        (fun i => ι (((P : Matrix (Fin n) (Fin n) L) *ᵥ x) i)) ∈ GlobalTheory.InertSph.latAt X v) →
      ∀ (g : UA σ X.J) (K K' : Matrix (Fin n) (Fin n) L), (∀ i j, K i j ∈ Formalism.UG.intL L) →
        (∀ i j, K' i j ∈ Formalism.UG.intL L) →
        mat g = (1 - ι 1) • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) +
          ((P : Matrix (Fin n) (Fin n) L) * K * ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)).map ι →
        mat g⁻¹ = (1 - ι 1) • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) +
          ((P : Matrix (Fin n) (Fin n) L) * K' * ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)).map ι →
        g ∈ GlobalTheory.InertSph.KAt σ X v := by
  intro F E _ _ _ _ _ σ v n X L _ _ ι _hinj hsurj hmul _hint P hP g K K' hK hK' hg hg'
  refine ⟨?_, fun z hz => ⟨mulVec_mem_latAt X v ι hsurj hmul P hP K hK _ hg z hz,
    mulVec_mem_latAt X v ι hsurj hmul P hP K' hK' _ hg' z hz⟩⟩
  have hsup : ∀ w u, evFin F v u = 0 → u • ι w = 0 := fun w => (hsurj (ι w)).2 ⟨w, rfl⟩
  intro u hu
  set N := (P : Matrix (Fin n) (Fin n) L) * K * ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
  have hm : mat g - 1 = (N - 1).map ι := by
    rw [hg]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.one_apply, map_sub]
      ring
    · simp [Matrix.one_apply, hij]
  rw [hm]
  ext i j
  simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.zero_apply]
  exact hsup _ u hu

end GlobalTheory.InertKatFrame
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertLocFrame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]

theorem frame_mul_map (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (hmul : ∀ x y, ι (x * y) = ι x * ι y) {m k : ℕ}
    (A : Matrix (Fin m) (Fin m) L) (Y : Matrix (Fin m) (Fin k) L) :
    ((1 - ι 1) • (1 : Matrix (Fin m) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) + A.map ι) * Y.map ι = (A * Y).map ι := by
  rw [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul]
  ext i j

  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, sub_mul, one_mul, ← hmul, one_mul, sub_self,
  zero_add, Matrix.mul_apply, Matrix.map_apply, Matrix.mul_apply, map_sum]
  simp only [Matrix.map_apply, hmul]

theorem map_mul_frame_transpose (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (hmul : ∀ x y, ι (x * y) = ι x * ι y) {m k : ℕ}
    (C : Matrix (Fin k) (Fin k) L) (Y : Matrix (Fin m) (Fin k) L) :
    Y.map ι * ((1 - ι 1) • (1 : Matrix (Fin k) (Fin k) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) + C.map ι)ᵀ = (Y * Cᵀ).map ι := by
  rw [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one]
  ext i j

  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, sub_mul, one_mul, ← hmul, one_mul, sub_self,
  zero_add, Matrix.mul_apply, Matrix.map_apply, Matrix.mul_apply, map_sum]
  simp only [Matrix.map_apply, Matrix.transpose_apply, hmul]

theorem actAB_xm_frame (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (L : Type) [Field L]
    (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (hmul : ∀ x y, ι (x * y) = ι x * ι y)
    (PV : GL (Fin n) L) (PW : GL (Fin d) L) (A : Matrix (Fin n) (Fin n) L) (C : Matrix (Fin d) (Fin d) L)
    (g : UA σ X.J) (h : UA σ W.J)
    (hg : mat g = (1 - ι 1) • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) + A.map ι)
    (hh : mat h = (1 - ι 1) • (1 : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) + C.map ι) (x : Matrix (Fin d) (Fin n) L) :
    actAB (cA σ) (g, h) (xm ι PV PW x) =
      (A * (PV : Matrix (Fin n) (Fin n) L) * xᵀ * (PW : Matrix (Fin d) (Fin d) L)ᵀ * Cᵀ).map ι := by
  change mat g * xm ι PV PW x * (mat h)ᵀ = _
  rw [xm_apply, hg, hh, frame_mul_map ι hmul, map_mul_frame_transpose ι hmul]
  simp only [Matrix.mul_assoc]

end GlobalTheory.InertLocFrame

end
end
