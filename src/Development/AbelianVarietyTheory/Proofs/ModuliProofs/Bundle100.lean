module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsBasisOfIsField
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle024
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle087
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsPullCubicalOfIso
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle091
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle088
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle093
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.ExistsGenTransfer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open scoped Matrix Topology

namespace GlobalTheory.ThetaFamily

theorem exists_values_line (hT : Out.GlobalSectionsRankAlgClosed) (P : Out.PolAV (Sp ℂ)) :
    ∃ v : P.L.ι → (Sp ℂ ⟶ P.A.left) → ℂ, ∀ s : P.L.Sec, ∃ a : ℂ, ∀ i (x : Sp ℂ ⟶ P.A.left), x ≫ P.A.hom = 𝟙 _ →
      ⊤ ≤ x ⁻¹ᵁ P.L.U i → valAt' x (P.L.U i) (s.f i) = a * v i x := by
  obtain ⟨β, hβ⟩ := PowSec.exists_basis_sections hT ℂ P 1 le_rfl
  have i₀ : Fin (1 ^ P.g) := ⟨0, by simp⟩
  have su : ∀ {M : Type} [AddCommMonoid M] (q : Fin (1 ^ P.g) → M), ∑ i, q i = q i₀ := fun q =>
    Finset.sum_eq_single i₀ (fun a _ h => absurd (Fin.ext (by have := a.2; have := i₀.2; simp at *; omega)) h) (by simp)
  refine ⟨fun i x => valAt' x _ ((β i₀).f (fun _ => i)), fun s => ?_⟩
  obtain ⟨a, ha, -⟩ := hβ (secToPow s 1)
  refine ⟨a i₀, fun i x hx hi => ?_⟩
  have hi' : ⊤ ≤ x ⁻¹ᵁ (lbPow P.L 1).U (fun _ => i) := fun p hp => mem_powChart.2 (hi hp)
  have e := (congrArg (valAt' x _) ((ha (fun _ => i)).trans (su _))).trans ((valAt'_mul x _ _ _).trans
    (congrArg (· * _) (valAt'_constFn x _ hx _ _ hi')))
  refine Eq.trans ?_ e
  exact ((valAt'_res x _ (s.f i ^ 1) hi').trans (by rw [pow_one])).symm

theorem exists_values_line_fibre (hT : Out.GlobalSectionsRankAlgClosed) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {D : Datum H} {l : Level H} {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B} (o : Obj D l b s)
    (z : Sp ℂ ⟶ S) :
    ∃ v : (o.t.PP.L.pull (pullback.fst o.t.G.hom z)).ι → (Sp ℂ ⟶ pullback o.t.G.hom z) → ℂ,
      ∀ s : (o.t.PP.L.pull (pullback.fst o.t.G.hom z)).Sec, ∃ a : ℂ, ∀ i (x : Sp ℂ ⟶ pullback o.t.G.hom z),
        x ≫ pullback.snd _ _ = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ (o.t.PP.L.pull (pullback.fst o.t.G.hom z)).U i →
        valAt' x ((o.t.PP.L.pull (pullback.fst o.t.G.hom z)).U i) (s.f i) = a * v i x := by
  have h := isGrpPullback_pullback o.t.G z
  obtain ⟨hL, hr, ⟨c', w, g, -⟩, hs⟩ := Out.CubePf.cubePull S _ o.t.G _ (cubeMapOf h) o.t.PP o.t.cub
  have := o.t.semi.smooth
  have : Smooth ((Over.pullback z).obj o.t.G).hom :=
    MorphismProperty.of_isPullback (P := @Smooth) h.1 o.t.semi.smooth
  obtain ⟨am, kt⟩ := amplePt _ _ z _ _ _ h _ _ o.t.PP.isLB hL ⟨w, g⟩ o.ample o.ktriv
  have := o.t.semi.geomConnected
  have : GeometricallyConnected ((Over.pullback z).obj o.t.G).hom :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected) h.1 o.t.semi.geomConnected
  have : ConnectedSpace ((Over.pullback z).obj o.t.G).left :=
    GeometricallyConnected.geometrically_connectedSpace (f := ((Over.pullback z).obj o.t.G).hom) (𝟙 _) (𝟙 _)
      ((Over.pullback z).obj o.t.G).hom
      (IsPullback.of_horiz_isIso ⟨(Category.id_comp _).trans (Category.comp_id _).symm⟩)
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected ((Over.pullback z).obj o.t.G).hom
    (eSec ((Over.pullback z).obj o.t.G) (default : PrimeSpectrum ℂ))
  obtain ⟨-, ws, gs', -⟩ := hs o.t.sym
  exact exists_values_line hT
    { A := (Over.pullback z).obj o.t.G, g := d, smoothDim := hd, L := o.t.PP.L.pull (pullback.fst o.t.G.hom z),
      isLB := hL, ample := am, ktriv := kt
      isAb := ⟨inferInstance, inferInstance, MorphismProperty.of_isPullback (P := @IsProper) h.1 o.proper, ‹_›⟩
      rigid := ⟨_, hr⟩
      sym := fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩ }

theorem exists_ratio_fibre (hT : Out.GlobalSectionsRankAlgClosed) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {D : Datum H} {l : Level H} {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B} (o : Obj D l b s)
    (u : Sp ℂ ⟶ S) (V : S.Opens) (θ₀ : ∀ j, Γ(o.t.G.left, o.t.G.hom ⁻¹ᵁ V ⊓ o.t.PP.L.U j))
    (hθ₀ : θ₀ ∈ secOn o.t.PP.L (o.t.G.hom ⁻¹ᵁ V))
    (nz : ∀ y ∈ V, ∃ (x : o.t.G.left) (j : o.t.PP.L.ι), o.t.G.hom x = y ∧ x ∈ o.t.G.left.basicOpen (θ₀ j))
    (hu : ⊤ ≤ u ⁻¹ᵁ V) (σ : LB.Sec (o.t.PP.L.pull (pullback.fst o.t.G.hom u))) :
    ∃ a : ℂ, ∀ j (x : Sp ℂ ⟶ pullback o.t.G.hom u),
      x ≫ pullback.snd _ _ = 𝟙 _ → ⊤ ≤ (x ≫ pullback.fst _ _) ⁻¹ᵁ o.t.PP.L.U j →
      valAt' x ((o.t.PP.L.pull (pullback.fst o.t.G.hom u)).U (fun _ => j)) (σ.f (fun _ => j)) =
        a * valAt' (x ≫ pullback.fst _ _) (o.t.G.hom ⁻¹ᵁ V ⊓ o.t.PP.L.U j) (θ₀ j) := by
  have := o.t.semi.smooth
  have mem : ∀ x, pullback.fst o.t.G.hom u x ∈ o.t.G.hom ⁻¹ᵁ V := fun x =>
    (congrArg (fun q => q x ∈ V) (pullback.condition (f := o.t.G.hom) (g := u))).mpr (hu (Set.mem_univ _))
  obtain ⟨t, ht⟩ := HolSec.exists_sec_pull o.t.PP.L _ _ mem θ₀ hθ₀
  obtain ⟨v, hv⟩ := exists_values_line_fibre hT o u
  obtain ⟨g₀, j₀, hg₀, hb₀⟩ := nz _ (hu (Set.mem_univ (default : PrimeSpectrum ℂ)))
  obtain ⟨g, hg₁, -⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback o.t.G.hom u) g₀ _ hg₀
  obtain ⟨x₀, hx₀, hx₁⟩ := ComplexPoints.exists_point_mem (pullback.snd o.t.G.hom u)
    (Z := (pullback.fst o.t.G.hom u ⁻¹ᵁ o.t.G.left.basicOpen (θ₀ j₀) : Scheme.Opens _))
    (TopologicalSpace.Opens.isOpen _).isLocallyClosed ⟨g, by
      show pullback.fst o.t.G.hom u g ∈ o.t.G.left.basicOpen (θ₀ j₀)
      rw [hg₁]; exact hb₀⟩
  have hx₂ : ⊤ ≤ (x₀ ≫ pullback.fst o.t.G.hom u) ⁻¹ᵁ o.t.G.left.basicOpen (θ₀ j₀) := fun p _ => hx₁ p
  obtain ⟨c, hc⟩ := hv t
  obtain ⟨a, ha⟩ := hv σ
  have m : ∀ j (x : Sp ℂ ⟶ pullback o.t.G.hom u), ⊤ ≤ (x ≫ pullback.fst _ _) ⁻¹ᵁ o.t.PP.L.U j →
      ⊤ ≤ x ⁻¹ᵁ (o.t.PP.L.pull (pullback.fst o.t.G.hom u)).U (fun _ => j) := fun j x h p hp => mem_pull.2 (h hp)
  have hj₀ : ⊤ ≤ (x₀ ≫ pullback.fst o.t.G.hom u) ⁻¹ᵁ o.t.PP.L.U j₀ :=
    top_le_preimage_mono _ ((o.t.G.left.basicOpen_le _).trans inf_le_right) hx₂
  have hc0 : c ≠ 0 := by
    rintro rfl
    refine (top_le_preimage_basicOpen_iff _ _ _).1 hx₂ ?_
    rw [← ht j₀ x₀ hj₀, hc _ x₀ hx₀ (m _ _ hj₀), zero_mul]
  refine ⟨a / c, fun j x h₁ h₂ => ?_⟩
  rw [← ht j x h₂, hc _ x h₁ (m _ _ h₂), ha _ x h₁ (m _ _ h₂)]
  field_simp

theorem exists_sec_const_mul {X : Scheme.{0}} {L : LB X} (p : X ⟶ Sp ℂ) (s : L.Sec) (a : ℂ) :
    ∃ t : L.Sec, ∀ i (x : Sp ℂ ⟶ X), x ≫ p = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ L.U i →
      valAt' x (L.U i) (t.f i) = a * valAt' x (L.U i) (s.f i) := by
  refine ⟨⟨fun i => constFn p _ a * s.f i, fun i j => ?_⟩, fun i x hx hi =>
    (valAt'_mul x _ _ _).trans (congrArg (· * _) (valAt'_constFn x _ hx _ _ hi))⟩
  rw [map_mul, map_mul, s.compat i j, mul_left_comm]
  congr 2
  have r : ∀ (U W : X.Opens) (h : W ≤ U), (X.presheaf.map (homOfLE h).op).hom (constFn p U a) = constFn p W a :=
    fun U W h => (congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a))
      (Scheme.Hom.appLE_map p (U := ⊤) (V := U) le_top (homOfLE h).op) :)
  rw [r, r]

theorem thetaChar_ne_zero {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} (hp : (τ.map Complex.im).PosDef) (a b : Fin g → ℝ) :
    thetaChar τ (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) ≠ 0 := by
  have hs : ((2 : ℂ)⁻¹ • (τ + τᵀ)).IsSymm := by
    rw [Matrix.IsSymm, Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_transpose, add_comm]
  have hi : ((2 : ℂ)⁻¹ • (τ + τᵀ)).map Complex.im = τ.map Complex.im := by
    ext i j
    have := congrFun (congrFun hp.1 i) j
    simp at this
    simp [this]
    ring
  have h := CanTh.thetaChar_ne_zero hs (hi ▸ hp) a b
  have e : ∀ v : Fin g → ℂ, v ⬝ᵥ ((2 : ℂ)⁻¹ • (τ + τᵀ)) *ᵥ v = v ⬝ᵥ τ *ᵥ v := fun v => by
    rw [Matrix.smul_mulVec, Matrix.add_mulVec, dotProduct_smul, dotProduct_add, Matrix.mulVec_transpose,
      dotProduct_comm v (v ᵥ* τ), ← Matrix.dotProduct_mulVec, smul_eq_mul]
    ring
  unfold thetaChar at h ⊢
  simpa only [e] using h

end GlobalTheory.ThetaFamily
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.HeckePoint

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {B : Type} [CommRing B] {b : Base l B} {k : Type} [Field k] {s : Sp k ⟶ Sp B}

def IsHeckeIsog (o o' : Obj D l b s) (p : ℕ) (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ o.t.G)) (ψ : o.t.G ⟶ o'.t.G) : Prop :=
  IsMonHom ψ ∧ (∀ a, o.t.act.act a ≫ ψ = ψ ≫ o'.t.act.act a) ∧
  (∀ y : 𝟙_ (Over (Sp k)) ⟶ o'.t.G, ∃ x, x ≫ ψ = y) ∧ (∀ x, x ≫ ψ = 1 ↔ x ∈ C) ∧
  (∀ (n : ℕ) (x x' : 𝟙_ (Over (Sp k)) ⟶ o.t.G) (c : kˣ), n.Coprime p → Out.WeilIs o.t.G o.t.PP.L n x x' (unitOn c) →
    Out.WeilIs o'.t.G o'.t.PP.L n (x ≫ ψ) (x' ≫ ψ) (unitOn (c ^ (p ^ 2)))) ∧
  ∀ p' : ℕ, p * p' ≡ 1 [MOD l.M'] → ∀ a, o.eta (p' • a) ≫ ψ = o'.eta a ∧ o.etaA (p' • a) ≫ ψ = o'.etaA a

theorem exists_inv_mod {p n : ℕ} (hp : p.Prime) (h : ¬ p ∣ n) : ∃ p', p * p' ≡ 1 [MOD n] := by
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_of_coprime 1 ((Nat.Prime.coprime_iff_not_dvd hp).2 h)
    (by rintro rfl; exact h (dvd_zero p))
  exact ⟨m, hm⟩

theorem natCast_M_mem (l : Level H) : (l.M : 𝓞 E) ∈ l.Mb := by
  have h : (l.M : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    rw [l.prod]; exact Ideal.mem_span_singleton_self _
  exact (Ideal.mul_le_inf h).1

theorem eq_of_modEq {A Q : Type} [AddCommGroup A] [Group Q] (f : A → Q) (hf : ∀ a c, f (a + c) = f a * f c) {n : ℕ}
    (hn : ∀ a, f (n • a) = 1) {p₁ p₂ : ℕ} (h : p₁ ≡ p₂ [MOD n]) (a : A) : f (p₁ • a) = f (p₂ • a) := by
  have key : ∀ q : ℕ, f (q • a) = f ((q % n) • a) := fun q => by
    conv_lhs => rw [← Nat.mod_add_div q n, add_nsmul, hf, mul_nsmul', hn, _root_.mul_one]
  rw [key p₁, key p₂, h]

theorem eta_M (o : Obj D l b s) (a : D.La) : o.eta (l.M • a) = 1 :=
  o.eta_ker _ (by
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
    exact Submodule.smul_mem_smul (natCast_M_mem l) Submodule.mem_top)

theorem modEq_of_inv {p p₁ p₂ n : ℕ} (h₁ : p * p₁ ≡ 1 [MOD n]) (h₂ : p * p₂ ≡ 1 [MOD n]) : p₁ ≡ p₂ [MOD n] := by
  calc p₁ = p₁ * 1 := (Nat.mul_one _).symm
    _ ≡ p₁ * (p * p₂) [MOD n] := h₂.symm.mul_left _
    _ = (p * p₁) * p₂ := by ring
    _ ≡ 1 * p₂ [MOD n] := h₁.mul_right _
    _ = p₂ := Nat.one_mul _

theorem comp_act_natCast {O : Type} [CommRing O] {S : Scheme.{0}} {G : Over S} [GrpObj G] (a : OAct O G) {T : Over S}
    (x : T ⟶ G) (n : ℕ) : x ≫ a.act (n : O) = x ^ n := by
  induction n with
  | zero =>
    have h := a.add 0 0
    rw [add_zero] at h
    rw [Nat.cast_zero, pow_zero, left_eq_mul.1 h, MonObj.comp_one]
  | succ n ih => rw [Nat.cast_succ, a.add, MonObj.comp_mul, ih, a.one, Category.comp_id, pow_succ]



theorem exists_isHeckeIsog [IsAlgClosed k] [CharZero k] (hL : Out.Laws)
    (hfacts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), IsAbelianScheme o.t.G ∧ SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p + D.q)) o.t.G.hom ∧ Out.Rigidified o.t.G o.t.PP.L ∧ Out.Sym o.t.G o.t.PP.L)
    (hTate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (𝔓 : Ideal (𝓞 E)) (p : ℕ) (k : Type) [Field k] (Q Q' : Type) [CommGroup Q] [CommGroup Q'] (act : 𝓞 E → Q → Q) (act' : 𝓞 E → Q' → Q') (e : ℕ → Q → Q → kˣ → Prop) (e' : ℕ → Q' → Q' → kˣ → Prop) (I : TateIso D k Q act e) (ψ : Q →* Q'), 𝔓.IsMaximal → 𝔓 ⊔ 𝔓.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ → p.Prime → (p : 𝓞 E) ∈ 𝔓 → Function.Surjective ψ → (∀ a x, ψ (act a x) = act' a (ψ x)) → (∀ J : Ideal (𝓞 E), J * 𝔓 = Ideal.span {(p : 𝓞 E)} → ∀ x, x ^ p = 1 → (∀ a ∈ J, act a x = 1) → ψ x = 1) → (∀ x, ψ x = 1 → x ^ p ^ 2 = 1 ∧ ∀ a ∈ Ideal.span {(p : 𝓞 E)} * 𝔓.map (H.bar : 𝓞 E →+* 𝓞 E), act a x = 1) → (∀ x y, ψ x = 1 → ψ y = 1 → e (p ^ 2) x y 1) → Nat.card ψ.ker = p ^ (2 * (Module.finrank ℚ E / 2 * (D.p + D.q))) → (∀ n x y c c', 0 < n → x ^ n = 1 → y ^ n = 1 → e n x y c → e n x y c' → c = c') → (∀ n x y c, 0 < n → ψ x ^ n = 1 → ψ y ^ n = 1 → e (n * p ^ 2) x y c → e' n (ψ x) (ψ y) c) → ∃ I' : TateIso D k Q' act' e', I'.ζ = I.ζ ∧ ∀ n p' : ℕ, 0 < n → p * p' ≡ 1 [MOD n] → ∀ a, I'.ev n a = ψ (I.ev n (p' • a)))
    (hQuot : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (t : SAB H (Sp k)) (g p : ℕ) (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ t.G)), 0 < p → IsProper t.G.hom → SmoothOfRelativeDimension g t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → (∀ x ∈ C, ∀ a, x ≫ t.act.act a ∈ C) → (∀ x ∈ C, x ^ p ^ 2 = 1) → (∀ x ∈ C, ∀ y ∈ C, Out.WeilIs t.G t.PP.L ((p ^ 2 : ℕ) : ℤ) x y 1) → Nat.card C = p ^ (2 * g) → ∃ (t' : SAB H (Sp k)) (ψ : t.G ⟶ t'.G), IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L ∧ Out.KTriv t'.G t'.PP.L ∧ IsMonHom ψ ∧ IsFinite ψ.left ∧ Etale ψ.left ∧ Surjective ψ.left ∧ (∀ x : 𝟙_ (Over (Sp k)) ⟶ t.G, x ≫ ψ = 1 ↔ x ∈ C) ∧ (∀ a, t.act.act a ≫ ψ = ψ ≫ t'.act.act a) ∧ LBIso (lbPow t.PP.L (p ^ 2)) (t'.PP.L.pull ψ.left))
    (hWeil : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (ψ : A ⟶ B) (L : LB A.left) (M : LB B.left) (d : ℕ) (n : ℤ) (T : Over S) (x y : T ⟶ A) (c c' : Γ(T.left, ⊤)ˣ), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → IsMonHom ψ → LBIso (lbPow L d) (M.pull ψ.left) → Out.WeilIs B M n (x ≫ ψ) (y ≫ ψ) c' → Out.WeilIs A L (n * d) x y c' ∧ (Out.WeilIs A L n x y c → c' = c ^ d))
    (hLie : ∀ (O : Type) [CommRing O] (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (ψ : A ⟶ B) (a : OAct O A) (b : OAct O B), IsMonHom ψ → Etale ψ.left → (∀ c, a.act c ≫ ψ = ψ ≫ b.act c) → ∀ (k : Type) [Field k] (x : Sp k ⟶ S) (τ : O →+* k) (n : ℕ), LieMult a x τ n ↔ LieMult b x τ n)
    (o : Obj D l b s) (𝔓 : Ideal (𝓞 E)) (p : ℕ) (h𝔓 : 𝔓.IsMaximal)
    (hco : 𝔓 ⊔ 𝔓.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤) (hp : p.Prime) (hp𝔓 : (p : 𝓞 E) ∈ 𝔓) (hpM : ¬ p ∣ l.M')
    (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ o.t.G)) (c₁ : ∀ x ∈ C, ∀ a, x ≫ o.t.act.act a ∈ C)
    (c₂ : ∀ J : Ideal (𝓞 E), J * 𝔓 = Ideal.span {(p : 𝓞 E)} → ∀ x, (∀ a ∈ J, x ≫ o.t.act.act a = 1) → x ∈ C)
    (c₃ : ∀ x ∈ C, ∀ a ∈ Ideal.span {(p : 𝓞 E)} * 𝔓.map (H.bar : 𝓞 E →+* 𝓞 E), x ≫ o.t.act.act a = 1)
    (c₄ : ∀ x ∈ C, ∀ y ∈ C, Out.WeilIs o.t.G o.t.PP.L ((p ^ 2 : ℕ) : ℤ) x y 1)
    (c₅ : Nat.card C = p ^ (2 * (Module.finrank ℚ E / 2 * (D.p + D.q)))) :
    (∀ x ∈ C, x ^ p ^ 2 = 1) ∧ ∃ (o' : Obj D l b s) (ψ : o.t.G ⟶ o'.t.G), IsHeckeIsog o o' p C ψ ∧
      IsFinite ψ.left ∧ Etale ψ.left ∧ Surjective ψ.left := by
  have hC : ∀ x ∈ C, x ^ p ^ 2 = 1 := fun x hx => by
    rw [← comp_act_natCast o.t.act]
    refine c₃ x hx _ ?_
    rw [Nat.cast_pow, pow_two]
    refine Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) ?_
    have := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hp𝔓
    rwa [map_natCast] at this
  refine ⟨hC, ?_⟩
  obtain ⟨hab, hdim, -, -⟩ := hfacts E H D l B b _ s o
  obtain ⟨t', ψ, hpr, ham, hkt, hhom, hfin, het, hsur, hker, hlin, hiso⟩ :=
    hQuot E H k o.t _ p C hp.pos o.proper hdim o.ample o.ktriv c₁ hC c₄ c₅
  obtain ⟨g', hg'⟩ := exists_dim t'
  let P := polOf o.t o.proper o.ample o.ktriv hdim
  let P' := polOf t' hpr ham hkt hg'
  have hab' := isAbelianScheme_of_proper t' hpr
  have := o.proper
  have hW := fun (n : ℤ) (T : Over (Sp k)) (x y : T ⟶ o.t.G) c c' =>
    hWeil _ o.t.G t'.G ψ o.t.PP.L t'.PP.L (p ^ 2) n T x y c c' hab hab' o.t.PP.isLB t'.PP.isLB hhom hiso
  obtain ⟨p₀, hp₀⟩ := exists_inv_mod hp hpM
  have hpow : IsMonHom (𝟙 o.t.G ^ p ^ 2) := by
    rw [← comp_act_natCast o.t.act, Category.id_comp]; exact o.t.act.hom _
  obtain ⟨gm₀, hgm⟩ := exists_fac hab.smooth ψ (𝟙 o.t.G ^ p ^ 2) fun x hx => by
    rw [MonObj.comp_pow, Category.comp_id]; exact hC x ((hker x).1 hx)
  have hgm₁ : ∀ (T : Over (Sp k)) (x : T ⟶ o.t.G), x ≫ ψ = 1 → x ^ p ^ 2 = 1 := fun T x hx => by
    calc x ^ p ^ 2 = (x ≫ ψ) ≫ gm₀ := by rw [Category.assoc, hgm, MonObj.comp_pow, Category.comp_id]
      _ = (1 ≫ ψ) ≫ gm₀ := by rw [hx, MonObj.one_comp ψ]
      _ = 1 := by rw [Category.assoc, hgm, MonObj.one_comp]
  have hMM : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
  have hAM : l.A ∣ l.M' := Nat.dvd_lcm_right _ _
  let o' : Obj D l b s :=
    { t := t', proper := hpr, ample := ham, ktriv := hkt
      eta := fun a => o.eta (p₀ • a) ≫ ψ
      eta_add := fun a c => by rw [smul_add, o.eta_add, MonObj.mul_comp]
      eta_ker := fun a ha => by rw [o.eta_ker _ (nsmul_mem ha _), MonObj.one_comp]
      etaA := fun a => o.etaA (p₀ • a) ≫ ψ
      etaA_add := fun a c => by rw [smul_add, o.etaA_add, MonObj.mul_comp]
      etaA_ker := fun a => by rw [smul_comm, o.etaA_ker, MonObj.one_comp]
      geom := by
        intro K _ _ x β hx
        obtain ⟨hdet, I, hζ, hA, hM⟩ := o.geom K x β hx
        refine ⟨fun τ => ?_, ?_⟩
        · simp only [← hLie _ _ _ _ ψ o.t.act t'.act hhom het hlin K x τ]
          exact hdet τ
        have hK : ∀ n : ℕ, 0 < n → (n : K) ≠ 0 := fun n hn => by
          have := ((b.unit n hn).map β).ne_zero
          rwa [map_natCast] at this
        let ψx : (Over.mk x ⟶ o.t.G) →* (Over.mk x ⟶ t'.G) :=
          MonoidHom.mk' (fun z => z ≫ ψ) fun a c => MonObj.mul_comp a c ψ
        have desc : ∀ (n : ℕ) (z : Over.mk x ⟶ o.t.G), 0 < n → z ^ n = 1 →
            ∃ z₀ : 𝟙_ (Over (Sp k)) ⟶ o.t.G, toUnit (Over.mk x) ≫ z₀ = z := fun n z hn hz =>
          exists_of_torsion hL.mulN P x (Nat.cast_ne_zero.2 hn.ne') (hK n hn) z hz
        have one : ∀ {G : Over (Sp k)} [GrpObj G] (z₀ : 𝟙_ (Over (Sp k)) ⟶ G),
            toUnit (Over.mk x) ≫ z₀ = 1 → z₀ = 1 := fun z₀ h =>
          toUnit_comp_injective x _ (h.trans (MonObj.comp_one _).symm)
        have kerd : ∀ z : Over.mk x ⟶ o.t.G, z ≫ ψ = 1 → ∃ z₀ ∈ C, toUnit (Over.mk x) ≫ z₀ = z := fun z hz => by
          obtain ⟨z₀, rfl⟩ := desc _ z (pow_pos hp.pos 2) (hgm₁ _ z hz)
          exact ⟨z₀, (hker z₀).1 (one _ ((Category.assoc _ _ _).symm.trans hz)), rfl⟩
        have uniq : ∀ (n : ℕ) (z w : Over.mk x ⟶ o.t.G) (c c' : Kˣ), z ^ n = 1 → w ^ n = 1 →
            Out.WeilIs o.t.G o.t.PP.L n z w (unitOn c) → Out.WeilIs o.t.G o.t.PP.L n z w (unitOn c') → c = c' :=
          fun n z w c c' hz hw h h' => (unitOn_bijective K).1 (((hL.weil _ P n _).1 z w hz hw).unique h h')
        have iso : ∀ z w : Over.mk x ⟶ o.t.G, z ≫ ψ = 1 → w ≫ ψ = 1 →
            Out.WeilIs o.t.G o.t.PP.L ((p ^ 2 : ℕ) : ℤ) z w (unitOn (1 : Kˣ)) := fun z w hz hw => by
          have h₁ : Out.WeilIs t'.G t'.PP.L ((1 : ℕ) : ℤ) (1 : Over.mk x ⟶ t'.G) 1 1 :=
            (hL.weil _ P' 1 (Over.mk x)).2.2.1 1 (one_pow _)
          have h₀ : Out.WeilIs t'.G t'.PP.L ((1 : ℕ) : ℤ) (z ≫ ψ) (w ≫ ψ) 1 := by rw [hz, hw]; exact h₁
          have h₂ := (hW ((1 : ℕ) : ℤ) _ z w 1 1 h₀).1
          rw [Nat.cast_one, _root_.one_mul] at h₂
          exact (congrArg (Out.WeilIs o.t.G o.t.PP.L ((p ^ 2 : ℕ) : ℤ) z w) unitOn_one).mpr h₂
        obtain ⟨I', hζ', hev⟩ := hTate E H D 𝔓 p K _ _ _ (fun a g => g ≫ t'.act.act a) _
          (fun n g g' c => Out.WeilIs t'.G t'.PP.L n g g' (unitOn c)) I ψx h𝔓 hco hp hp𝔓
          (fun y => exists_lift_pt ψ x y)
          (fun a z => by
            show (z ≫ _) ≫ ψ = (z ≫ ψ) ≫ _
            rw [Category.assoc, hlin, Category.assoc])
          (fun J hJ z hz hz' => by
            obtain ⟨z₀, rfl⟩ := desc _ z hp.pos hz
            show (_ ≫ z₀) ≫ ψ = 1
            rw [Category.assoc, (hker z₀).2 (c₂ J hJ z₀ fun a ha =>
              one _ ((Category.assoc _ _ _).symm.trans (hz' a ha))), MonObj.comp_one])
          (fun z hz => ⟨hgm₁ _ z hz, fun a ha => by
            obtain ⟨z₀, h₀, rfl⟩ := kerd z hz
            show (_ ≫ z₀) ≫ _ = 1
            rw [Category.assoc, c₃ z₀ h₀ a ha, MonObj.comp_one]⟩)
          (fun z w hz hw => iso z w hz hw)
          (by
            rw [← c₅]
            refine (Nat.card_congr (Equiv.ofBijective (fun z : C => (⟨toUnit (Over.mk x) ≫ z.1, by
              show (_ ≫ z.1) ≫ ψ = 1
              rw [Category.assoc, (hker _).2 z.2, MonObj.comp_one]⟩ : ψx.ker)) ⟨fun a c h =>
                Subtype.ext (toUnit_comp_injective x _ (congrArg Subtype.val h)), fun z => ?_⟩)).symm
            obtain ⟨z₀, h₀, e⟩ := kerd z.1 z.2
            exact ⟨⟨z₀, h₀⟩, Subtype.ext e⟩)
          (fun n z w c c' _ hz hw h h' => uniq n z w c c' hz hw h h')
          (fun n z w c hn hz hw h => by
            obtain ⟨c', hc', -⟩ := (hL.weil _ P' n (Over.mk x)).1 (z ≫ ψ) (w ≫ ψ) hz hw
            obtain ⟨c', rfl⟩ := (unitOn_bijective K).2 c'
            have h₂ := (hW n _ z w 1 _ hc').1
            rw [← Nat.cast_mul] at h₂
            have t : ∀ u : Over.mk x ⟶ o.t.G, ψx u ^ n = 1 → u ^ (n * p ^ 2) = 1 := fun u hu => by
              rw [pow_mul]; exact hgm₁ _ _ ((map_pow ψx u n).trans hu)
            rw [uniq _ z w c c' (t z hz) (t w hw) h h₂]
            exact hc')
        refine ⟨I', by rw [hζ']; exact hζ, fun a => ?_, fun a ha => ?_⟩
        · rw [hev l.A p₀ l.A_pos (hp₀.of_dvd hAM), ← hA, ← Category.assoc]; rfl
        · rw [hev l.M p₀ (by have := l.three_le; omega) (hp₀.of_dvd hMM), ← hM _ (nsmul_mem ha _), ← Category.assoc]; rfl }
  refine ⟨o', ψ, ⟨hhom, hlin, fun y => exists_lift_pt ψ (𝟙 _) y, hker, fun n x x' c hn h => ?_, fun p' hp' a => ?_⟩,
    hfin, het, hsur⟩
  · have hn₀ : 0 < n := Nat.pos_of_ne_zero (by
      rintro rfl
      exact hp.one_lt.ne' ((Nat.coprime_zero_left p).1 hn))
    have : Unique (𝟙_ (Over (Sp k))).left := inferInstanceAs (Unique (PrimeSpectrum k))
    obtain ⟨t₁, t₂⟩ := pow_eq_one_of_weilIs hL.kerPow P hn₀ h
    obtain ⟨c', hc', -⟩ := (hL.weil _ P' n _).1 (x ≫ ψ) (x' ≫ ψ)
      (by rw [← MonObj.pow_comp, t₁, MonObj.one_comp]) (by rw [← MonObj.pow_comp, t₂, MonObj.one_comp])
    have e := (hW n _ x x' _ _ hc').2 h
    rw [unitOn_pow]
    exact e ▸ hc'
  · have e := modEq_of_inv hp' hp₀
    exact ⟨congrArg (· ≫ ψ) (eq_of_modEq o.eta o.eta_add (eta_M o) (e.of_dvd hMM) a),
      congrArg (· ≫ ψ) (eq_of_modEq o.etaA o.etaA_add o.etaA_ker (e.of_dvd hAM) a)⟩

end GlobalTheory.HeckePoint
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory

theorem lbIso_lam_pull_id_w0 {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}}
    (t : SAB H S) :
    LBIso t.PP.L ((abelian₂ t.G t.PP.L).pull (Y := t.G.left) (lift (𝟙 t.G) (t.act.act H.w0)).left) := by
  have hΛ : (abelian₂ t.G t.PP.L).IsLB := LB.isLB_linComb t.PP.isLB _ _
  refine t.prim.trans t.PP.isLB (LB.isLB_linComb t.PP.isLB _ _) (LB.isLB_pull hΛ _) ?_
  refine LBIso.chartPull (A := abelian₂ t.G t.PP.L) (B := abelian₂ t.G t.PP.L) (h := (lift (𝟙 t.G) (t.act.act H.w0)).left)
    (chartPullSame t.PP.L _ _ _ _ fun I => ?_) (Geo.Tor.chartPullPull _ _ _ rfl) (Pdiv.PullbackComparison.gen_refl _ hΛ)
  have e : psum t.G ![𝟙 t.G, t.act.act H.w0] I.down =
      lift (𝟙 t.G) (t.act.act H.w0) ≫ psum t.G (x2 t.G) I.down := by
    refine Eq.trans (congrArg (fun z => psum t.G z I.down) (funext fun i => ?_))
      (psum_hom (preHom (lift (𝟙 t.G) (t.act.act H.w0))) (x2 t.G) I.down).symm
    fin_cases i
    · exact (lift_fst _ _).symm
    · exact (lift_snd _ _).symm
  exact congrArg (fun z => z.left) e

theorem exists_sabMap_of_isProper_of_lbIso_lam : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (t : SAB H S) (t' : SAB H S') (f : S' ⟶ S) (φ : t'.G.left ⟶ t.G.left) (φ₂ : (G2 t'.G).left ⟶ (G2 t.G).left), IsProper t.G.hom → IsGrpPullback t'.G t.G f φ → IsSquare φ φ₂ → LBIso (abelian₂ t'.G t'.PP.L) ((abelian₂ t.G t.PP.L).pull φ₂) → (∀ a, (t'.act.act a).left ≫ φ = φ ≫ (t.act.act a).left) → ∃ m : SABMap t' t f, m.φ = φ := by
  intro hL E _ _ _ H S S' t t' f φ φ₂ hp gp sq hΛ hact
  refine exists_sabMap_of_isProper_of_lbIso hL.globalFns E H S S' t t' f φ hp gp ?_ hact
  have l : (abelian₂ t.G t.PP.L).IsLB := LB.isLB_linComb t.PP.isLB _ _
  have l' : (abelian₂ t'.G t'.PP.L).IsLB := LB.isLB_linComb t'.PP.isLB _ _
  let δ : t.G.left ⟶ (G2 t.G).left := (lift (𝟙 t.G) (t.act.act H.w0)).left
  let δ' : t'.G.left ⟶ (G2 t'.G).left := (lift (𝟙 t'.G) (t'.act.act H.w0)).left
  have a₁ : δ ≫ (fst t.G t.G).left = 𝟙 _ := congrArg (fun z => z.left) (lift_fst (𝟙 t.G) (t.act.act H.w0))
  have a₂ : δ ≫ (snd t.G t.G).left = (t.act.act H.w0).left :=
    congrArg (fun z => z.left) (lift_snd (𝟙 t.G) (t.act.act H.w0))
  have b₁ : δ' ≫ (fst t'.G t'.G).left = 𝟙 _ := congrArg (fun z => z.left) (lift_fst (𝟙 t'.G) (t'.act.act H.w0))
  have b₂ : δ' ≫ (snd t'.G t'.G).left = (t'.act.act H.w0).left :=
    congrArg (fun z => z.left) (lift_snd (𝟙 t'.G) (t'.act.act H.w0))
  have e : δ' ≫ φ₂ = φ ≫ δ := by
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst t.G t.G).left = (_ ≫ _) ≫ (fst t.G t.G).left
      rw [Category.assoc, sq.1, ← Category.assoc, b₁, Category.assoc, a₁, Category.id_comp, Category.comp_id]
    · show (_ ≫ _) ≫ (snd t.G t.G).left = (_ ≫ _) ≫ (snd t.G t.G).left
      rw [Category.assoc, sq.2, ← Category.assoc, b₂, Category.assoc, a₂, hact]
  have s₁ : LBIso t'.PP.L (((abelian₂ t.G t.PP.L).pull φ₂).pull δ') :=
    (lbIso_lam_pull_id_w0 t').trans t'.PP.isLB (LB.isLB_pull l' _) (LB.isLB_pull (LB.isLB_pull l _) _)
      (SiegelPullComp.iso_pull δ' hΛ)
  have s₂ : LBIso t'.PP.L ((abelian₂ t.G t.PP.L).pull (δ' ≫ φ₂)) :=
    s₁.trans t'.PP.isLB (LB.isLB_pull (LB.isLB_pull l _) _) (LB.isLB_pull l _) (SiegelPullComp.iso_pull_pull l φ₂ δ')
  rw [e] at s₂
  have s₃ : LBIso t'.PP.L (((abelian₂ t.G t.PP.L).pull δ).pull φ) :=
    s₂.trans t'.PP.isLB (LB.isLB_pull l _) (LB.isLB_pull (LB.isLB_pull l _) _) (SiegelPullComp.iso_pull_pull l δ φ).symm
  exact s₃.trans t'.PP.isLB (LB.isLB_pull (LB.isLB_pull l _) _) (LB.isLB_pull t.PP.isLB _)
    (SiegelPullComp.iso_pull φ (lbIso_lam_pull_id_w0 t)).symm

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

theorem _root_.GlobalTheory.T.exists_cmTripleMap_descend_groupQuotient : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Γ : Type) [Group Γ] [Finite Γ] (U U' X' : Scheme.{0}) (ρ : Γ →* Aut U) (r : U ⟶ U') (t : SAB H U) (t' : SAB H U') (t₁ : SAB H X') (τ : Γ →* Aut t.G.left) (ν : SABMap t t' r) (j : U' ⟶ X') (n : SABMap t t₁ (r ≫ j)), (IsAffineHom r ∧ (∀ g, (ρ g).asIso.hom ≫ r = r) ∧ ∀ V : U'.Opens, Function.Injective (r.app V).hom ∧ ∀ f : Γ(U, r ⁻¹ᵁ V), (∀ g (h : r ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (r ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (r.app V).hom) → IsReduced U → IsProper t.G.hom → (∀ g, (τ g).asIso.hom ≫ t.G.hom = t.G.hom ≫ (ρ g).asIso.hom ∧ (τ g).asIso.hom ≫ ν.φ = ν.φ ∧ (τ g).asIso.hom ≫ n.φ = n.φ) → ∃ n' : SABMap t' t₁ j, ν.φ ≫ n'.φ = n.φ := by
  first | exact @GlobalTheory.exists_sabMap_of_quotient | exact GlobalTheory.exists_sabMap_of_quotient | (intros; apply GlobalTheory.exists_sabMap_of_quotient <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem _root_.GlobalTheory.T.weilPairing_fieldExtension_iff : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (K Ω : Type) [Field K] [Field Ω] (i : K →+* Ω) (x : Sp K ⟶ S) (L : LB G.left) (k : ℤ) (y y' : Over.mk x ⟶ G) (c : Kˣ), IsAbelianScheme G → L.IsLB → (Out.WeilIs G L k ((Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) ≫ y) ((Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) ≫ y') (unitOn (Units.map i.toMonoidHom c)) ↔ Out.WeilIs G L k y y' (unitOn c)) := by
  first | exact @GlobalTheory.weilIs_fieldExt_iff | exact GlobalTheory.weilIs_fieldExt_iff | (intros; apply GlobalTheory.weilIs_fieldExt_iff <;> assumption)
end
