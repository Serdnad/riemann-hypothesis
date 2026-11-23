module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle777
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3072
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle925
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2672
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHostUnitAddConjEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataBaseChangeSymmetric
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle624
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfIso

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

theorem _root_.GlobalTheory.T.factor_periods_projection_period_points : ∀ (R : Type) [CommRing R] [IsDomain R] (D₀ D' : DegPre R), D'.TauBimult → ∀ (O : Type) [Ring O] [StarRing O] [Module O D'.X] (o : D'.OAct O) (e f : O) (inc : D₀.P.A ⟶ D'.P.A) (pr : D'.P.A ⟶ D₀.P.A) (h : D₀.X →+ D'.X) (φ : D'.X →+ D₀.X), IsMonHom inc → IsMonHom pr → pr ≫ inc = o.onB.act e → (∀ χ, ∃ u : LB.Gen (CmpLB D' D₀ pr (h χ) χ), Nrm u) → LBIso (abelian₂ D₀.P.A D₀.P.L) ((abelian₂ D'.P.A D'.P.L).pull (lift (fst D₀.P.A D₀.P.A ≫ inc) (snd D₀.P.A D₀.P.A ≫ inc ≫ o.onB.act f) : G2 D₀.P.A ⟶ G2 D'.P.A).left) → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F], (∀ (y : D'.X) (g : GtPtF D' F), GtPtF.IsIota y g → ∃ g' : GtPtF D₀ F, Act D' D₀ pr h g g' ∧ GtPtF.IsIota (φ y) g') → (∀ y, h (φ y) = star e • f • e • y) → (∀ y, D₀.c (φ y) = D'.c y ≫ pr) ∧ ∃ w : LB.Iso (abelian₂ D₀.P.A D₀.P.L) ((abelian₂ D'.P.A D'.P.L).pull (lift (fst D₀.P.A D₀.P.A ≫ inc) (snd D₀.P.A D₀.P.A ≫ inc ≫ o.onB.act f) : G2 D₀.P.A ⟶ G2 D'.P.A).left), w.IsGen ∧ ∀ y y' z J J', Good D'.P.L z J → Good D₀.P.L z J' → val (D₀.tau (φ y) (φ y')) (𝟙 _) z J' = GlobalTheory.PolDeg.lamVal w (lift (toUnit (TK R) ≫ D₀.c (φ y)) (toUnit (TK R) ≫ D₀.c (φ y'))).left z J J' * val (D'.tau (e • y) (f • e • y')) (𝟙 _) z J := by
  first | exact @GlobalTheory.Mum.Two.Fac.periods_of_factor | exact GlobalTheory.Mum.Two.Fac.periods_of_factor | (intros; apply GlobalTheory.Mum.Two.Fac.periods_of_factor <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

theorem _root_.GlobalTheory.T.harrisTaylor_lie_tate_loci_closed_siegelPullback : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (h M : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Scheme.{0}) (s₁ : S ⟶ Sp B) (t : S ⟶ Sp R) (c : SiegPre h M ζ s₁) (e : ℕ), e.Coprime p → SiegKerBy c e → ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (πX : X ⟶ S) (AX : Over X) [GrpObj AX] [IsCommMonObj AX] (φX : AX.left ⟶ c.A.left) (φ₂X : (G2 AX).left ⟶ (G2 c.A).left) (actX : OActN D.O AX) (ηX : D.La → (𝟙_ (Over X) ⟶ AX)), IsGrpPullback AX c.A πX φX → IsSquare φX φ₂X → RosatiFor D actX (c.P.pull φ₂X) → EtaOK D N actX ηX → ∃ (Z : Scheme.{0}) (j : Z ⟶ X), IsClosedImmersion j ∧ ∀ (T : Scheme.{0}) (g : T ⟶ X), (∃ z : T ⟶ Z, z ≫ j = g) ↔ ((∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ T), x ≫ g ≫ πX ≫ t = spMap β → LieHer b actX β (x ≫ g)) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T) (β : R →+* k), x ≫ g ≫ πX ≫ t = spMap β → GeomAt D N actX (c.P.pull φ₂X) ηX k (x ≫ g)) := by
  first | (exact @GlobalTheory.UPel.HT.lieGeom_locus_closed) | (exact GlobalTheory.UPel.HT.lieGeom_locus_closed) | (intros; apply GlobalTheory.UPel.HT.lieGeom_locus_closed  <;> assumption)
end

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt

theorem exists_eq_nsmul_of_forall_ef_dvd {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {n : ℕ} (hn : 0 < n) (a : D.La) (h : ∀ b, (n : ℤ) ∣ D.EF a b) : ∃ e, a = n • e := by
  choose c hc using h
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  let ψ : D.La →+ ℤ := AddMonoidHom.mk' c fun x y => mul_left_cancel₀ hn' (by rw [mul_add, ← hc, ← hc, ← hc, map_add (f := _)])
  obtain ⟨e, he⟩ := D.unimod.2 ψ.toIntLinearMap
  refine ⟨e, D.unimod.1 (LinearMap.ext fun b => ?_)⟩
  rw [map_nsmul, he, hc, LinearMap.smul_apply, nsmul_eq_mul]
  rfl

theorem exists_shear_of_adjoint : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {X : Type}
    [AddCommGroup X] [Module (𝓞 E) X]
    (y : D.La →ₗ[𝓞 E] X) (n N : ℕ), 0 < n → N ∣ n → Cois D y n → ∀ Z Z' : Submodule (𝓞 E) D.La, IsOpp D Z Z' →
    ∀ σ w : D.La →ₗ[𝓞 E] D.La, (∀ a, σ a ∈ Z') → (∀ b ∈ Z', σ b = b) → (∀ a, ∃ e, y (σ a) = y a + n • e) →
    (∀ a, ∃ b ∈ perp D Z, ∃ e, σ a = a + b + N • e) → (∀ a b, D.EF (w a) b = D.EF a (σ b)) →
    (∀ b ∈ Z', (∃ e, y b = n • e) → ∃ e ∈ Z', b = n • e) →
    ∃ t : Z →ₗ[𝓞 E] D.La, (∀ z : Z, ∃ e ∈ perp D Z', t z = (z : D.La) + N • e) ∧ (∀ z z' : Z, D.EF (t z) (t z') = 0) ∧
      ∀ (z : Z) (a : D.La), (∃ e, y a = n • e) → (n : ℤ) ∣ D.EF (t z) a := by
  intro E _ _ _ H D X _ _ y n N hn hNn hC Z Z' hO σ w hσZ hσb hσy hσN hw hsat
  have hN : 0 < N := Nat.pos_of_dvd_of_pos hNn hn
  obtain ⟨k, hk⟩ := hNn
  have hnZ : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'

  have ha : ∀ z ∈ Z, ∃ e ∈ perp D Z', w z = z + N • e := by
    intro z hz
    obtain ⟨e, he⟩ := exists_eq_nsmul_of_forall_ef_dvd D hN (w z - z) fun b => by
      obtain ⟨b', hb', e, he⟩ := hσN b
      have h0 : D.EF z b' = 0 := by rw [ef_swap, hb' z hz, neg_zero]
      refine ⟨D.EF z e, ?_⟩
      simp only [map_sub, LinearMap.sub_apply, hw, he, map_add (f := _), map_nsmul, h0, nsmul_eq_mul]
      ring
    refine ⟨e, mem_perp.2 fun b hb => ?_, (sub_eq_iff_eq_add'.1 he)⟩
    have h1 : D.EF (w z - z) b = 0 := by rw [map_sub, LinearMap.sub_apply, hw, hσb b hb, sub_self]
    rw [he, map_nsmul, LinearMap.smul_apply, smul_eq_zero] at h1
    exact h1.resolve_left hN.ne'

  have hb : ∀ z a : D.La, (∃ e, y a = n • e) → (n : ℤ) ∣ D.EF (w z) a := by
    rintro z a ⟨e, he⟩
    obtain ⟨e₁, he₁⟩ := hσy a
    obtain ⟨e', -, he'⟩ := hsat (σ a) (hσZ a) ⟨e + e₁, by rw [he₁, he, smul_add]⟩
    refine ⟨D.EF z e', ?_⟩
    rw [hw, he', map_nsmul, nsmul_eq_mul]
  have hwy : ∀ z, ∃ e, y (w z) = n • e := fun z => hC.2 (w z) fun b hb' => hb z b hb'
  have hww : ∀ z z', (n : ℤ) ∣ D.EF (w z) (w z') := fun z z' => hb z (w z') (hwy z')
  obtain ⟨f, hf⟩ : ∃ f : Z → Z → ℤ, ∀ z z', (n : ℤ) * f z z' = D.EF (w z) (w z') :=
    ⟨fun z z' => D.EF (w z) (w z') / n, fun z z' => Int.mul_ediv_cancel' (hww _ _)⟩
  obtain ⟨β, hβ⟩ : ∃ β : LinearMap.BilinForm ℤ Z, ∀ a b, β a b = f a b :=
    ⟨LinearMap.mk₂ ℤ f
      (fun z₁ z₂ z' => mul_left_cancel₀ hnZ (by rw [mul_add, hf, hf, hf]; simp))
      (fun c z z' => mul_left_cancel₀ hnZ (by rw [smul_eq_mul, mul_left_comm, hf, hf]; simp))
      (fun z z₁ z₂ => mul_left_cancel₀ hnZ (by rw [mul_add, hf, hf, hf]; simp))
      (fun c z z' => mul_left_cancel₀ hnZ (by rw [smul_eq_mul, mul_left_comm, hf, hf]; simp)),
      fun _ _ => rfl⟩
  have hskew : ∀ a b, β a b = -β b a := fun a b => by
    rw [hβ, hβ]
    exact mul_left_cancel₀ hnZ (by rw [mul_neg, hf, hf, ef_swap])
  have hadj : ∀ (c : 𝓞 E) a b, β (c • a) b = β a (H.bar c • b) := fun c a b => by
    rw [hβ, hβ]
    exact mul_left_cancel₀ hnZ (by rw [hf, hf, Submodule.coe_smul, Submodule.coe_smul, w.map_smul, w.map_smul, D.adj])
  obtain ⟨c, hc⟩ := exists_skew_solve hO.2.2.1 β hskew hadj
  have ht : ∀ z : Z, (w ∘ₗ Z.subtype - n • (Z'.subtype ∘ₗ c)) z = w z - n • (c z : D.La) := fun z => rfl
  refine ⟨w ∘ₗ Z.subtype - n • (Z'.subtype ∘ₗ c), fun z => ?_, fun z z' => ?_, fun z a ha' => ?_⟩
  · obtain ⟨e₁, he₁, hwz⟩ := ha z z.2
    refine ⟨e₁ - k • (c z : D.La), sub_mem he₁ (nsmul_mem (hO.2.1 (c z).2) k), ?_⟩
    rw [ht, hwz, hk, smul_sub, mul_smul]
    abel
  · have e1 : D.EF (w z) (c z') = D.EF z (c z') := by rw [hw, hσb _ (c z').2]
    have e2 : D.EF (c z) (w z') = D.EF (c z) z' := by rw [ef_swap, hw, hσb _ (c z).2, ← ef_swap]
    have e3 : D.EF (c z) (c z') = 0 := hO.2.1 (c z).2 _ (c z').2
    have e4 : (n : ℤ) * β z z' = D.EF (w z) (w z') := by rw [hβ, hf]
    have e5 := hc z z'
    rw [ht, ht]
    simp only [map_sub, map_nsmul, LinearMap.sub_apply, LinearMap.smul_apply, nsmul_eq_mul, e1, e2, e3]
    linear_combination (-1 : ℤ) * e4 - (n : ℤ) * e5
  · rw [ht, map_sub, map_nsmul, LinearMap.sub_apply, LinearMap.smul_apply, nsmul_eq_mul]
    exact dvd_sub (hb z a ha') (dvd_mul_right _ _)

end GlobalTheory.LowFilt
end
end

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt.Opp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem proj_quot_of_sat {R M : Type} [CommRing R] [IsDedekindDomain R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (N : Submodule R M) (h : ∀ a : R, a ≠ 0 → ∀ y : M, a • y ∈ N → y ∈ N) :
    Module.Projective R (M ⧸ N) := by
  have htor : Submodule.torsion R (M ⧸ N) = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun u hu => ?_
    obtain ⟨⟨a, ha⟩, hau⟩ := (Submodule.mem_torsion_iff u).1 hu
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    rw [Submonoid.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hau
    rw [Submodule.Quotient.mk_eq_zero]
    exact h a (nonZeroDivisors.ne_zero ha) y hau
  have : Module.Flat R (M ⧸ N) := IsDedekindDomain.flat_iff_torsion_eq_bot.2 htor
  have : Module.FinitePresentation R (M ⧸ N) := Module.finitePresentation_of_finite _ _
  exact Module.Flat.projective_of_finitePresentation

theorem exists_ef_eq (D : Datum H) (ψ : D.La →+ ℤ) : ∃ y : D.La, ∀ x, D.EF y x = ψ x := by
  obtain ⟨y, hy⟩ := D.unimod.2 ψ.toIntLinearMap
  exact ⟨y, fun x => by rw [hy]; rfl⟩

theorem fin_int (D : Datum H) : Module.Finite ℤ D.La := by
  haveI := D.fin
  exact Module.Finite.trans (𝓞 E) D.La

variable {D : Datum H} {Z : Submodule (𝓞 E) D.La}

theorem sat_int (hZ : IsIsoSat D Z) (n : ℤ) (hn : n ≠ 0) (y : D.La) (hy : n • y ∈ Z) : y ∈ Z := by
  refine hZ.2 n.natAbs y (by omega) ?_
  rcases Int.natAbs_eq n with h1 | h1
  · rw [← natCast_zsmul, ← h1]; exact hy
  · have : ((n.natAbs : ℤ)) • y = -(n • y) := by rw [h1]; simp
    rw [← natCast_zsmul, this]; exact Z.neg_mem hy

theorem proj_int (hZ : IsIsoSat D Z) : Module.Projective ℤ (D.La ⧸ Z.restrictScalars ℤ) := by
  haveI := fin_int D
  exact proj_quot_of_sat _ fun a ha y hy => sat_int hZ a ha y hy

theorem exists_ext (hZ : IsIsoSat D Z) (φ : Z →+ ℤ) : ∃ y : D.La, ∀ z : Z, D.EF z y = φ z := by
  haveI := proj_int hZ
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property (Z.restrictScalars ℤ).mkQ LinearMap.id
    (Submodule.mkQ_surjective _)
  have hmem : ∀ x : D.La, x - σ ((Z.restrictScalars ℤ).mkQ x) ∈ Z := fun x => by
    have : (Z.restrictScalars ℤ).mkQ (x - σ ((Z.restrictScalars ℤ).mkQ x)) = 0 := by
      rw [map_sub, ← LinearMap.comp_apply, hσ, LinearMap.id_apply, sub_self]
    exact (Submodule.Quotient.mk_eq_zero _).1 this
  obtain ⟨y, hy⟩ := exists_ef_eq D (AddMonoidHom.mk' (fun x => φ ⟨_, hmem x⟩) fun x x' => by
    rw [← map_add (f := _)]; congr 1; ext; simp only [map_add (f := _), Submodule.coe_add]; abel)
  refine ⟨-y, fun z => ?_⟩
  have h0 : (Z.restrictScalars ℤ).mkQ (z : D.La) = 0 := (Submodule.Quotient.mk_eq_zero _).2 z.2
  rw [map_neg, ef_swap, neg_neg, hy]
  simp only [AddMonoidHom.mk'_apply, h0, map_zero, sub_zero]

theorem mem_of_perp_perp (hZ : IsIsoSat D Z) (y : D.La) (hy : ∀ p ∈ perp D Z, D.EF y p = 0) : y ∈ Z := by
  haveI := proj_int hZ
  by_contra hyZ
  have hu : (Z.restrictScalars ℤ).mkQ y ≠ 0 := fun h => hyZ ((Submodule.Quotient.mk_eq_zero _).1 h)
  obtain ⟨χ, hχ⟩ : ∃ χ : Module.Dual ℤ (D.La ⧸ Z.restrictScalars ℤ), χ ((Z.restrictScalars ℤ).mkQ y) ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hu ((Module.forall_dual_apply_eq_zero_iff ℤ _).1 hc)
  obtain ⟨p, hp⟩ := exists_ef_eq D (χ.comp (Z.restrictScalars ℤ).mkQ).toAddMonoidHom
  have hpZ : p ∈ perp D Z := fun z hz => by
    have h0 : (Z.restrictScalars ℤ).mkQ z = 0 := (Submodule.Quotient.mk_eq_zero _).2 hz
    rw [hp, LinearMap.toAddMonoidHom_coe, LinearMap.comp_apply, h0, map_zero]
  have := hy p hpZ
  rw [ef_swap, hp, neg_eq_zero] at this
  exact hχ this

theorem perp_sat (D : Datum H) (Z : Submodule (𝓞 E) D.La) (a : 𝓞 E) (ha : a ≠ 0) (y : D.La) (hy : a • y ∈ perp D Z) :
    y ∈ perp D Z := by
  have hne : (Ideal.span {a}).comap (algebraMap ℤ (𝓞 E)) ≠ ⊥ :=
    Ideal.comap_ne_bot_of_integral_mem ha (Ideal.mem_span_singleton_self a) (Algebra.IsIntegral.isIntegral a)
  obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨a', ha'⟩ := Ideal.mem_span_singleton'.1 (Ideal.mem_comap.1 hn)
  intro z hz
  have h := (perp D Z).smul_mem a' hy z hz
  rw [smul_smul, ha', algebraMap_int_eq, eq_intCast, Int.cast_smul_eq_zsmul, map_zsmul, LinearMap.smul_apply,
    smul_eq_mul] at h
  exact (mul_eq_zero.1 h).resolve_left hn0

theorem exists_opp (D : Datum H) (Z : Submodule (𝓞 E) D.La) (hZ : IsIsoSat D Z) : ∃ Z' : Submodule (𝓞 E) D.La, IsOpp D Z Z' := by
  haveI := D.fin
  haveI : Module.Projective (𝓞 E) (D.La ⧸ perp D Z) := proj_quot_of_sat _ (perp_sat D Z)
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (perp D Z).mkQ LinearMap.id (Submodule.mkQ_surjective _)
  have hsx : ∀ q, (perp D Z).mkQ (s q) = q := fun q => by rw [← LinearMap.comp_apply, hs, LinearMap.id_apply]
  set C := LinearMap.range s with hC
  have hdec : ∀ x : D.La, x - s ((perp D Z).mkQ x) ∈ perp D Z := fun x =>
    (Submodule.Quotient.mk_eq_zero _).1 (by rw [← Submodule.mkQ_apply, map_sub, hsx, sub_self])
  have hC0 : ∀ c ∈ C, c ∈ perp D Z → c = 0 := by
    rintro _ ⟨q, rfl⟩ h
    have : q = 0 := by rw [← hsx q]; exact (Submodule.Quotient.mk_eq_zero _).2 h
    rw [this, map_zero]
  have hsC : ∀ c ∈ C, s ((perp D Z).mkQ c) = c := by
    rintro _ ⟨q, rfl⟩; rw [hsx]
  have hZx : ∀ (z : D.La), z ∈ Z → ∀ x, D.EF z x = D.EF z (s ((perp D Z).mkQ x)) := fun z hz x => by
    have := hdec x z hz
    rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at this
    rw [ef_swap, this, ← ef_swap]
  have A1 : ∀ φ : Z →+ ℤ, ∃! b : C, ∀ a : Z, D.EF a b = φ a := by
    intro φ
    obtain ⟨y, hy⟩ := exists_ext hZ φ
    refine ⟨⟨s ((perp D Z).mkQ y), _, rfl⟩, fun a => (hZx a a.2 y).symm.trans (hy a), fun b hb => Subtype.ext ?_⟩
    have h1 : (b : D.La) - s ((perp D Z).mkQ y) ∈ perp D Z := fun z hz => by
      rw [ef_swap, map_sub, hb ⟨z, hz⟩, ← hZx z hz, hy ⟨z, hz⟩, sub_self, neg_zero]
    exact sub_eq_zero.1 (hC0 _ (sub_mem b.2 ⟨_, rfl⟩) h1)

  have A2 : ∀ φ : C →+ ℤ, ∃! z : Z, ∀ c : C, D.EF c z = φ c := by
    intro φ
    have hmC : ∀ x : D.La, s ((perp D Z).mkQ x) ∈ C := fun x => ⟨_, rfl⟩
    obtain ⟨y, hy⟩ := exists_ef_eq D (AddMonoidHom.mk' (fun x => φ ⟨_, hmC x⟩) fun x x' => by
      rw [← map_add (f := _)]; congr 1; ext; simp only [map_add (f := _), Submodule.coe_add])
    simp only [AddMonoidHom.mk'_apply] at hy
    have hyZ : -y ∈ Z := mem_of_perp_perp hZ _ fun p hp => by
      have h0 : (perp D Z).mkQ p = 0 := (Submodule.Quotient.mk_eq_zero _).2 hp
      rw [map_neg, LinearMap.neg_apply, hy]
      have : (⟨s ((perp D Z).mkQ p), hmC p⟩ : C) = 0 := Subtype.ext (by show s ((perp D Z).mkQ p) = 0; rw [h0, map_zero])
      rw [this, map_zero, neg_zero]
    have key : ∀ c : C, D.EF c (-y) = φ c := fun c => by
      rw [ef_swap, map_neg, LinearMap.neg_apply, neg_neg, hy]
      congr 1; exact Subtype.ext (hsC c c.2)
    refine ⟨⟨-y, hyZ⟩, key, fun z hz => Subtype.ext ?_⟩
    have hw : ∀ x, D.EF ((z : D.La) - -y) x = 0 := fun x => by
      have h1 := hz ⟨_, hmC x⟩
      have h2 := key ⟨_, hmC x⟩
      rw [hZx _ (sub_mem z.2 hyZ), ef_swap, map_sub]
      rw [h1, h2, sub_self, neg_zero]
    exact sub_eq_zero.1 (D.unimod.1 (LinearMap.ext fun x => by rw [hw, map_zero, LinearMap.zero_apply]))
  let β : LinearMap.BilinForm ℤ C := LinearMap.mk₂ ℤ (fun a b : C => -D.EF a b)
    (fun a a' b => by simp only [Submodule.coe_add, map_add (f := _), LinearMap.add_apply]; abel) (fun n a b => by simp) (fun a b b' => by simp only [Submodule.coe_add, map_add (f := _)]; abel) (fun n a b => by simp)
  obtain ⟨t, ht⟩ := exists_skew_solve A2 β (fun a b => by
      show -D.EF a b = -(-D.EF b a)
      rw [ef_swap D a b]) (fun c a b => by
      show -D.EF ((c • a : C) : D.La) b = -D.EF a ((H.bar c • b : C) : D.La)
      rw [Submodule.coe_smul, Submodule.coe_smul, D.adj])
  have ht' : ∀ a b : C, D.EF a (t b) + D.EF (t a) b = -D.EF a b := ht
  let g : C →ₗ[𝓞 E] D.La := C.subtype + Z.subtype ∘ₗ t
  have hg : ∀ c, g c = c + t c := fun c => rfl
  have kZ : ∀ (a : Z) (c : C), D.EF a (g c) = D.EF a c := fun a c => by
    rw [hg, map_add (f := _), hZ.1 a.2 _ (t c).2, add_zero]
  refine ⟨LinearMap.range g, hZ.1, ?_, fun φ => ?_, fun φ => ?_⟩
  · rintro _ ⟨b, rfl⟩ _ ⟨b', rfl⟩
    show D.EF (g b) (g b') = 0
    have h0 : D.EF (t b) (t b') = 0 := hZ.1 (t b).2 _ (t b').2
    rw [hg, hg]
    simp only [map_add (f := _), LinearMap.add_apply]
    linear_combination ht' b b' + h0
  · obtain ⟨b, hb, hu⟩ := A1 φ
    refine ⟨⟨g b, b, rfl⟩, fun a => (kZ a b).trans (hb a), ?_⟩
    rintro ⟨_, b', rfl⟩ hb'
    exact Subtype.ext (congrArg g (hu b' fun a => (kZ a b').symm.trans (hb' a)))
  · obtain ⟨a, ha, hu⟩ := A2 (-(φ.comp g.rangeRestrict.toAddMonoidHom))
    refine ⟨a, ?_, fun a' ha' => hu a' fun c => ?_⟩
    · rintro ⟨_, c, rfl⟩
      show D.EF a (g c) = φ ⟨g c, c, rfl⟩
      rw [kZ, ef_swap, ha c, AddMonoidHom.neg_apply, neg_neg]
      rfl
    · have h1 := ha' ⟨g c, c, rfl⟩
      rw [ef_swap, ← kZ a' c]
      show -D.EF a' (g c) = -φ ⟨g c, c, rfl⟩
      rw [← h1]

end GlobalTheory.LowFilt.Opp
end
end

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {Z Z' : Submodule (𝓞 E) D.La}

theorem IsOpp.proj_unique (h : IsOpp D Z Z') {a b b' : D.La} (hb : b ∈ Z') (hb' : b' ∈ Z')
    (h1 : a - b ∈ perp D Z) (h2 : a - b' ∈ perp D Z) : b = b' := by
  have := h.eq_zero (sub_mem hb hb') (by
    have := sub_mem h2 h1
    rwa [sub_sub_sub_cancel_left] at this)
  exact sub_eq_zero.1 this

def IsOpp.proj (h : IsOpp D Z Z') : D.La →ₗ[𝓞 E] Z' where
  toFun a := ⟨(h.exists_sub_mem_perp a).choose, (h.exists_sub_mem_perp a).choose_spec.1⟩
  map_add' a b := by
    have ha := (h.exists_sub_mem_perp a).choose_spec
    have hb := (h.exists_sub_mem_perp b).choose_spec
    have hab := (h.exists_sub_mem_perp (a + b)).choose_spec
    apply Subtype.ext
    refine h.proj_unique hab.1 (add_mem ha.1 hb.1) hab.2 ?_
    have := add_mem ha.2 hb.2
    simpa [sub_add_sub_comm] using this
  map_smul' c a := by
    have ha := (h.exists_sub_mem_perp a).choose_spec
    have hca := (h.exists_sub_mem_perp (c • a)).choose_spec
    apply Subtype.ext
    refine h.proj_unique hca.1 (Z'.smul_mem c ha.1) hca.2 ?_
    have := (perp D Z).smul_mem c ha.2
    simpa [smul_sub] using this

theorem IsOpp.sub_proj_mem (h : IsOpp D Z Z') (a : D.La) : a - h.proj a ∈ perp D Z :=
  (h.exists_sub_mem_perp a).choose_spec.2

theorem IsOpp.proj_eq (h : IsOpp D Z Z') {a b : D.La} (hb : b ∈ Z') (hab : a - b ∈ perp D Z) : (h.proj a : D.La) = b :=
  h.proj_unique (h.proj a).2 hb (h.sub_proj_mem a) hab

theorem IsOpp.proj_of_mem (h : IsOpp D Z Z') {b : D.La} (hb : b ∈ Z') : (h.proj b : D.La) = b :=
  h.proj_eq hb (by simp)

theorem IsOpp.proj_of_perp (h : IsOpp D Z Z') {a : D.La} (ha : a ∈ perp D Z) : (h.proj a : D.La) = 0 :=
  h.proj_eq Z'.zero_mem (by simpa using ha)

variable (D)

theorem exists_adjoint (σ : D.La →ₗ[𝓞 E] D.La) : ∃ w : D.La →ₗ[𝓞 E] D.La, ∀ a b, D.EF (w a) b = D.EF a (σ b) := by
  choose w hw using fun a => D.unimod.2 ((D.EF a).comp (σ.restrictScalars ℤ))
  refine ⟨{ toFun := w, map_add' := fun a b => D.unimod.1 ?_, map_smul' := fun c a => D.unimod.1 ?_ }, fun a b => ?_⟩
  · ext x; simp [hw]
  · ext x
    simp only [hw, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars, RingHom.id_apply, D.adj]
    rw [← σ.map_smul]
  · exact congrArg (fun f => f b) (hw a)

theorem bijective_of_isometry (g : D.La →ₗ[𝓞 E] D.La) (hg : ∀ a b, D.EF (g a) (g b) = D.EF a b) :
    Function.Bijective g := by
  obtain ⟨w, hw⟩ := exists_adjoint D g
  have hwg : ∀ a, w (g a) = a := fun a => D.unimod.1 (LinearMap.ext fun b => by rw [hw, hg])
  have hws : Function.Surjective w := fun a => ⟨g a, hwg a⟩
  haveI := D.fin
  have hwi : Function.Injective w := OrzechProperty.injective_of_surjective_endomorphism w hws
  refine ⟨fun a b hab => by rw [← hwg a, ← hwg b, hab], fun a => ⟨w a, hwi (by rw [hwg])⟩⟩

def equivOfIsometry (g : D.La →ₗ[𝓞 E] D.La) (hg : ∀ a b, D.EF (g a) (g b) = D.EF a b) : D.La ≃ₗ[𝓞 E] D.La :=
  LinearEquiv.ofBijective g (bijective_of_isometry D g hg)

@[simp] theorem equivOfIsometry_apply (g : D.La →ₗ[𝓞 E] D.La) (hg : ∀ a b, D.EF (g a) (g b) = D.EF a b) (a : D.La) :
    equivOfIsometry D g hg a = g a := rfl

end GlobalTheory.LowFilt
end
end

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt

theorem exists_improves_of_perp {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] (y : D.La →ₗ[𝓞 E] X) (n : ℕ)
    (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z') (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal) (hn𝔭 : (n : 𝓞 E) ∈ 𝔭)
    (e : 𝓞 E) (he1 : e - 1 ∈ 𝔭) (he : ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → 𝔮 ≠ 𝔭 → e ∈ 𝔮)
    (v : Z') (hv : y v ∈ 𝔭 • (⊤ : Submodule (𝓞 E) X)) (ℓ₀ : Z' →ₗ[𝓞 E] 𝓞 E) (hℓ₀ : ℓ₀ v ∉ 𝔭)
    (m : D.La) (hm : m ∈ perp D Z ⊓ perp D Z') (hym : y m ∉ img D y Z' 𝔭)
    (hA : 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ 𝔭 ∨ Z.map y ≤ img D y Z' 𝔭) :
    ∃ Z'', Improves D y n 𝔭 Z Z' Z'' := by
  obtain ⟨θ, hθ⟩ := exists_theta_vec D m
  obtain ⟨ζ, hζZ, -, hζs, hopp⟩ := h.exists_rank_one hm θ hθ
  have himg' : ∀ I : Ideal (𝓞 E), img D y Z' I = LinearMap.range (y ∘ₗ Z'.subtype) ⊔ I • ⊤ := fun I => by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have himg'' : ∀ (ℓ : Z' →ₗ[𝓞 E] 𝓞 E) (I : Ideal (𝓞 E)),
      img D y (LinearMap.range (Z'.subtype + ℓ.smulRight (m + ζ ℓ))) I =
        LinearMap.range (y ∘ₗ Z'.subtype + ℓ.smulRight (y (m + ζ ℓ))) ⊔ I • ⊤ := fun ℓ I => by
    have : y ∘ₗ (Z'.subtype + ℓ.smulRight (m + ζ ℓ)) = y ∘ₗ Z'.subtype + ℓ.smulRight (y (m + ζ ℓ)) := by
      ext x; simp
    rw [img, ← LinearMap.range_comp, this]
  have he𝔭 : e ∉ 𝔭 := fun h' => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using sub_mem h' he1))
  have hℓv : (e • ℓ₀) v ∉ 𝔭 := by
    rw [LinearMap.smul_apply, smul_eq_mul]
    exact fun h' => (h𝔭.isPrime.mem_or_mem h').elim he𝔭 hℓ₀
  have hker := range_le_of_ker (y ∘ₗ Z'.subtype) (e • ℓ₀) (y (m + ζ (e • ℓ₀))) 𝔭 h𝔭 (v := v) hv hℓv
  refine ⟨_, hopp (e • ℓ₀), fun 𝔮 h𝔮 hn𝔮 => ?_, ?_⟩
  · rw [himg', himg'']
    by_cases hq : 𝔮 = 𝔭
    · subst hq; exact hker.2
    · exact range_le_of_mem _ _ _ 𝔮 fun x => by
        rw [LinearMap.smul_apply, smul_eq_mul]; exact Ideal.mul_mem_right _ _ (he 𝔮 h𝔮 hn𝔮 hq)
  · rw [himg'']
    intro hle
    have hu' := hle hker.1
    have hz : y (ζ (e • ℓ₀)) ∈ img D y Z' 𝔭 := by
      rcases hA with hA | hA
      · haveI := h𝔭
        have h𝔭' : (𝔭.map (H.bar : 𝓞 E →+* 𝓞 E)).IsMaximal := Ideal.map_isMaximal_of_equiv H.bar
        have hn' : (n : 𝓞 E) ∈ 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) := by
          simpa using Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hn𝔭
        have he' := he _ h𝔭' hn' hA
        rw [Ideal.map_comap_of_equiv, Ideal.mem_comap] at he'
        have hbe : H.bar e ∈ 𝔭 := by
          have : H.bar.symm e = H.bar e := by rw [RingEquiv.symm_apply_eq, bar_bar]
          rwa [this] at he'
        rw [hζs, map_smul]
        exact Submodule.mem_sup_right (Submodule.smul_mem_smul hbe trivial)
      · exact hA (Submodule.mem_map_of_mem (hζZ _))
    apply hym
    have : y m = y (m + ζ (e • ℓ₀)) - y (ζ (e • ℓ₀)) := by simp
    rw [this]
    exact sub_mem hu' hz

end GlobalTheory.LowFilt
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HalfBC GlobalTheory.PrimCocycle

theorem _root_.GlobalTheory.T.exists_mumfordBundleIso_comp_cartesianHom_values : ∀ {S S' S₁ : Scheme.{0}} {B : Over S₁} {G : Over S} {G' : Over S'} [GrpObj B] [IsCommMonObj B] [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] {M : LB B.left} {L : LB G.left} {L' : LB G'.left} {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (gp : IsGrpPullback G' G f φ) {β₂ : (G2 G).left ⟶ (G2 B).left}, M.IsLB → L.IsLB → L'.IsLB → ∀ (w : LB.Iso (abelian₂ G L) ((abelian₂ B M).pull β₂)) (v : LB.Iso L' (L.pull φ)), w.IsGen → v.IsGen → ∃ w'' : LB.Iso (abelian₂ G' L') ((abelian₂ B M).pull (sqOf gp ≫ β₂)), w''.IsGen ∧ ∀ (Z : Scheme.{0}) (p : Z ⟶ (G2 G').left) (z : Z) (J : (Z ⟶ B.left) → M.ι) (J₁ : (Z ⟶ G.left) → L.ι) (J' : (Z ⟶ G'.left) → L'.ι), Good M z J → Good L z J₁ → Good L' z J' → lamVal w'' p z J J' = lamVal w (p ≫ sqOf gp) z J J₁ * ∏ I, gw v (p ≫ lamφ G' I) z (J₁ ((p ≫ lamφ G' I) ≫ φ)) (J' (p ≫ lamφ G' I)) ^ lamε I := by
  first | exact @GlobalTheory.TautPull.lamIso_comp_exists | exact GlobalTheory.TautPull.lamIso_comp_exists | (intros; apply GlobalTheory.TautPull.lamIso_comp_exists <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)


theorem _root_.GlobalTheory.T.periods_bounded_outside_cmType_of_definite_arc_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (N : ℕ) (U : Unf Xo c σ N) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : ℂ → (A →+* ℂ)) (r : ℝ) (y : ℂ → FrPt Xo c (CAt σ)) (k : U.Comp) (T : ℝ) (M : ℕ) (γ : GL (Fin N) E) (xx : ℂ → Frame (U.X k).Ψ N), GoodEmb c σ → IsUnf U → IsArc Z σ φ x ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → Matches fr (ψ u) (y u)) → IsOrbit (U.X k) T M γ xx → IsLift U k y T xx → (U.X k).p0 = 0 → ∀ v : Fin N → E, ∃ C : ℝ, ∀ᶠ w in imTop, ∀ (τ : E →+* ℂ) (i : ℕ), τ ∉ (U.X k).Ψ → ‖perFr (U.X k) (xx w) v τ i‖ ≤ C := by
  first | exact @GlobalTheory.ShFam.PerLim.periods_bounded_outside_cmType_of_definite_arc_lift_alt | exact GlobalTheory.ShFam.PerLim.periods_bounded_outside_cmType_of_definite_arc_lift_alt | (intros; apply GlobalTheory.ShFam.PerLim.periods_bounded_outside_cmType_of_definite_arc_lift_alt <;> assumption)
end
