module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2703
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2913
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2704
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2702
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2700
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2995
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle191
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle065
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2791
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2906
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2902
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2917
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2919
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2787
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2792
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2877
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle080
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2904
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2694
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2999
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2918
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.UniformityLowerBounds

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.QF

theorem polFib_transport {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} (hL : L.IsLB) {K : Type}
    [Field K] {x : Sp K ⟶ S} {P P' : PolAV (Sp K)} (φ : P'.A ≅ P.A) (hφ : IsPolIso P' P φ)
    {α : P.A.left ⟶ G.left} (hα : IsGrpPullback P.A G x α) (hLα : LBIso P.L (L.pull α)) :
    IsGrpPullback P'.A G x (φ.hom.left ≫ α) ∧ LBIso P'.L (L.pull (φ.hom.left ≫ α)) := by
  have := hφ.1
  refine ⟨((ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_of_iso φ).comp hα).congr (Category.id_comp _) rfl, ?_⟩
  obtain ⟨t, ht⟩ := hφ.2
  have h1 : LBIso P'.L (P.L.pull φ.hom.left) := LBIso.symm ⟨t, ht⟩
  have h2 : LBIso (P.L.pull φ.hom.left) (L.pull (φ.hom.left ≫ α)) :=
    LBIso.chartPull (chartPullPull P.L φ.hom.left)
      (chartPullSame L (fun _ : PUnit => φ.hom.left ≫ α) (fun _ => α) (fun _ => 1) φ.hom.left
        (fun _ => rfl)) hLα
  exact LBIso.trans P'.isLB (pull_isLB P.isLB _) (pull_isLB hL _) h1 h2

theorem charZero_of_pt {F K : Type} [Field F] [CharZero F] [Field K] (t : Sp K ⟶ Sp F) : CharZero K := by
  have f := (Spec.preimage t).hom
  exact (f.charZero_iff f.injective).1 inferInstance

end GlobalTheory.UMin.QF

namespace GlobalTheory.UMin.QF

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}

def ThetaData (Xo : Moduli Dw l) {K : Type} [Field K] (y : Sp K ⟶ Xo.X) (g m : ℕ) (ze : Γ(Sp K, ⊤)ˣ)
    (v : (Fin (2 * g) → ZMod (m ^ 2)) → Γ((baseOver (Sp K)).left, ⊤)) : Prop :=
  ∃ (P : PolAV (Sp K)) (hg : P.g = g) (α : P.A.left ⟶ Xo.univ.t.G.left) (lev : Out.Level P (m ^ 2) ze),
    IsGrpPullback P.A Xo.univ.t.G y α ∧ LBIso P.L (Xo.univ.t.PP.L.pull α) ∧ IsThetaPt P m (levelPoint lev hg) v

theorem finite_thetaData (Xo : Moduli Dw l) (c : Coeff l) (g j : ℕ) (hbig : 81 ^ g * g.factorial < 3 ^ j * 81)
    (K : Type) [Field K] [IsAlgClosed K] (h3 : ((3 : ℕ) : K) ≠ 0) (ze : Γ(Sp K, ⊤)ˣ) (x : Sp K ⟶ Xo.XF c)
    (v : (Fin (2 * g) → ZMod ((3 ^ j * 81) ^ 2)) → Γ((baseOver (Sp K)).left, ⊤)) :
    Set.Finite {y : Sp K ⟶ Xo.XF c | y ≫ pullback.snd _ _ = x ≫ pullback.snd _ _ ∧
      ThetaData Xo (y ≫ pullback.fst _ _) g (3 ^ j * 81) ze v} := by
  by_cases hne : ∃ y₀ : Sp K ⟶ Xo.XF c, y₀ ≫ pullback.snd _ _ = x ≫ pullback.snd _ _ ∧
      ThetaData Xo (y₀ ≫ pullback.fst _ _) g (3 ^ j * 81) ze v
  · obtain ⟨y₀, -, P₀, hg₀, -, lev₀, -, -, hθ₀⟩ := hne
    have hQ := GlobalTheory.T.unitaryModuli_finite_points_with_given_polarisedFibre E H Dw l Xo K P₀ (x ≫ pullback.fst _ _ ≫ Xo.s)
    refine Set.Finite.of_finite_image (f := fun y => y ≫ pullback.fst _ _) (hQ.subset ?_) ?_
    · rintro _ ⟨y, ⟨hys, P, hg, α, lev, hpb, hPL, hθ⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · show (y ≫ pullback.fst _ _) ≫ Xo.s = x ≫ pullback.fst _ _ ≫ Xo.s
        rw [Category.assoc, pullback.condition, ← Category.assoc, hys, Category.assoc, ← pullback.condition]
      · obtain ⟨φ, hφ, -⟩ := (GlobalTheory.T.thetaPoint_determines_and_end_determined_torsion).1 g 3 2 j 81 (3 ^ j * 81) Nat.prime_three (by decide) le_rfl
          (by norm_num) rfl hbig K h3 P₀ P hg₀ hg ze lev₀ lev v hθ₀ hθ
        exact ⟨φ.hom.left ≫ α, polFib_transport Xo.univ.t.PP.isLB φ hφ hpb hPL⟩
    · intro y₁ h₁ y₂ h₂ h
      exact pullback.hom_ext h (h₁.1.trans h₂.1.symm)
  · apply Set.Finite.subset Set.finite_empty
    intro y hy
    exact False.elim (hne ⟨y, hy⟩)

end GlobalTheory.UMin.QF

namespace GlobalTheory.UMin.QF

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}

theorem exists_thetaData (Xo : Moduli Dw l) (c : Coeff l) {o : Type} [CommRing o] {n j g : ℕ}
    (hg : g = Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) (f : Xo.XF c ⟶ PSpace o n)
    (hn : n + 1 = (3 ^ j * 81) ^ (4 * g))
    (hth : ThMap Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (3 ^ j * 81) (pullback.fst _ _ : Xo.XF c ⟶ Xo.X) f)
    (K : Type) [Field K] [IsAlgClosed K] (hm0 : ((3 ^ j * 81 : ℕ) : K) ≠ 0) (ze : Γ(Sp K, ⊤)ˣ)
    (hze : IsPrimitiveRoot ze ((3 ^ j * 81) ^ 2)) (x : Sp K ⟶ Xo.XF c) (e : Fin (n + 1) → K)
    (he : PCrd (x ≫ f) e) (T : Finset (Fin (n + 1) → K))
    (hT : ∀ (c : Fin (n + 1) → K) (a : K), a ≠ 0 → (∀ j, symTup c j = a * e j) →
      ∃ mu : K, mu ≠ 0 ∧ (fun b => mu * c b) ∈ T)
    (y : Sp K ⟶ Xo.XF c) (hy : y ≫ f = x ≫ f) :
    ∃ (t : T) (β : (Fin (2 * g) → ZMod ((3 ^ j * 81) ^ 2)) → Fin (n + 1)),
      ThetaData Xo (y ≫ pullback.fst _ _) g (3 ^ j * 81) ze (fun a => GlobalTheory.ZH.fn ((t : Fin (n + 1) → K) (β a))) := by
  have hodd : Odd (3 ^ j * 81) := (Odd.pow (by decide : Odd 3)).mul (by decide : Odd 81)
  have hLB := Xo.univ.t.PP.isLB
  have hρ := Xo.univ.t.PP.rigGen
  obtain ⟨P, α, hPg, hpb, hPL⟩ := GlobalTheory.T.universalTriple_fibre_principallyPolarised_dimension E H Dw l Xo c K (y ≫ pullback.fst _ _)
  rw [← hg] at hPg
  have hfib : PolFib Xo.univ.t.G Xo.univ.t.PP.L g (y ≫ pullback.fst _ _) := ⟨P, α, hPg, hpb, hPL⟩
  obtain ⟨⟨θ, hθ⟩, -⟩ := GlobalTheory.T.principallyPolarisedFibre_exists_generator_stable _ Xo.univ.t.G Xo.univ.t.PP.L hLB g K _ hfib
  obtain ⟨pt, cy, hcy⟩ := GlobalTheory.T.exists_thetaConstantList_algClosed _ Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig hLB hρ g (3 ^ j * 81) (n + 1) K
    _ θ hodd hm0 hn hfib
  have hH : HasTh Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (3 ^ j * 81) (y ≫ pullback.fst _ _) cy :=
    ⟨θ, pt, hθ, hcy⟩
  have hP1 : PCrd (y ≫ f) (symTup cy) := hth K y cy hH
  rw [hy] at hP1
  obtain ⟨a, ha0, ha⟩ := (GlobalTheory.T.projectiveHomogeneousCoords_field_determine_descend).2.1 o K n (x ≫ f) e (symTup cy) he hP1
  obtain ⟨mu, hmu0, hmuT⟩ := hT cy a ha0 ha
  haveI := P.isAb.comm
  obtain ⟨rig, hrig⟩ := P.rigid
  have hP : HasTh P.A P.L rig (3 ^ j * 81) (𝟙 (Sp K)) cy := by
    rw [hasTh_iff] at hH ⊢
    refine (GlobalTheory.T.hasThetaConstantsTwoLevels_move_cartesian _ Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig hLB hρ (Sp K) P.A P.L rig
      (y ≫ pullback.fst _ _) α P.isLB hrig hpb hPL (3 ^ j * 81) (3 ^ j * 81) (n + 1) (n + 1) K (𝟙 _) cy cy).2 ?_
    rwa [Category.id_comp]
  obtain ⟨lev, β, hβ⟩ := GlobalTheory.T.exists_level_thetaPoint_of_thetaConstants_level_square K P rig g (3 ^ j * 81) (n + 1) hPg cy ze hrig hodd hm0 hze hP
  exact ⟨⟨_, hmuT⟩, β, P, hPg, α, lev, hpb, hPL, hβ mu hmu0⟩

end GlobalTheory.UMin.QF

namespace GlobalTheory.UMin.QF

theorem finite_fibre_thMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (o : Type) [CommRing o] (j n : ℕ) (f : Xo.XF c ⟶ PSpace o n), 81 ^ (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)).factorial < 3 ^ j * 81 → n + 1 = (3 ^ j * 81) ^ (4 * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) → ThMap Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (3 ^ j * 81) (pullback.fst _ _ : Xo.XF c ⟶ Xo.X) f → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Xo.XF c), Set.Finite {y : Sp K ⟶ Xo.XF c | y ≫ pullback.snd _ _ = x ≫ pullback.snd _ _ ∧ y ≫ f = x ≫ f} := by
  intro E _ _ _ H Dw l Xo c o _ j n f hbig hn hth K _ _ x
  haveI : CharZero K := charZero_of_pt (x ≫ pullback.snd _ _)
  set g := Module.finrank ℚ E / 2 * (Dw.p + Dw.q) with hg
  have hm0 : ((3 ^ j * 81 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (by positivity)
  have h3 : ((3 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (by norm_num)
  have hpos : 0 < (3 ^ j * 81) ^ 2 := by positivity
  haveI : NeZero (((3 ^ j * 81) ^ 2 : ℕ) : K) := ⟨Nat.cast_ne_zero.2 hpos.ne'⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K ((3 ^ j * 81) ^ 2)
  let eK := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm
  have hz' := hz.map_of_injective eK.injective
  set ze : Γ(Sp K, ⊤)ˣ := (hz'.isUnit hpos.ne').unit with hzedef
  have hze : IsPrimitiveRoot ze ((3 ^ j * 81) ^ 2) := hz'.isUnit_unit hpos.ne'
  obtain ⟨⟨e, he⟩, -⟩ := (GlobalTheory.T.projectiveHomogeneousCoords_basic_properties).2.2 o K n (x ≫ f)
  obtain ⟨T, hT⟩ := GlobalTheory.T.thetaSymmetricFunctionsDegreeFactorial_scaled_finite K (n + 1) e
  haveI : NeZero ((3 ^ j * 81) ^ 2) := ⟨hpos.ne'⟩
  refine (Set.finite_iUnion fun d : T × ((Fin (2 * g) → ZMod ((3 ^ j * 81) ^ 2)) → Fin (n + 1)) =>
    finite_thetaData Xo c g j hbig K h3 ze x
      (fun a => GlobalTheory.ZH.fn ((d.1 : Fin (n + 1) → K) (d.2 a)))).subset ?_
  rintro y ⟨h1, h2⟩
  obtain ⟨t, β, hd⟩ := exists_thetaData Xo c hg f hn hth K hm0 ze hze x e he T hT y h2
  exact Set.mem_iUnion.2 ⟨(t, β), h1, hd⟩

end GlobalTheory.UMin.QF
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8

namespace GlobalTheory.Poinc.MatChar

theorem charMap_matrix : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (A₀ : PolAV (Sp (FractionRing V₁))) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G₀ → ∀ (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (D : DegData V₁ (maximalIdeal V₁)) (P : PolAV (Sp (FractionRing V₁))) (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V₁) D P G) (q : Fin 8 → (G ⟶ G₀)), (∀ u, IsMonHom (q u)) → ∀ c : Fin 8 → (D₀.toPre.X →+ D.toPre.X), (∀ u, TorMatch U₀ U (RingHom.id V₁) (q u).left (c u)) → ∀ (a : Matrix (Fin 8) (Fin 8) ℤ) (f : G ⟶ G) (m : D.toPre.X →+ D.toPre.X), IsMonHom f → EndChar U f m → (∀ u, f ≫ q u = (List.ofFn fun v => q v ^ a u v).prod) → ∀ u χ, m (c u χ) = ∑ v, a u v • c v χ := by
  intro V₁ _ _ _ hCN D₀ A₀ G₀ _ _ hG₀ U₀ D P G _ _ hG U q hq c hc a f m hf hm hfq u χ
  have hB : GlobalTheory.Mum.Base V₁ := ⟨⟨hCN.1, inferInstance, hCN.2.1, hCN.2.2.1⟩, hCN.2.2.2⟩
  obtain ⟨-, hone, hmul⟩ := GlobalTheory.Poinc.Eq8.torMatch_id_one_mul V₁ hB G₀ hG₀ D₀ A₀ U₀ G hG D P U
  have huniq : ∀ (β : G.left ⟶ G₀.left) (ρ ρ' : D₀.toPre.X →+ D.toPre.X), TorMatch U₀ U (RingHom.id V₁) β ρ →
      TorMatch U₀ U (RingHom.id V₁) β ρ' → ρ = ρ' := fun β ρ ρ' =>
    GlobalTheory.Poinc.Eq8.torMatch_unique V₁ hB G₀ hG₀ D₀ A₀ U₀ V₁ hB G hG D P U (RingHom.id V₁) β Function.injective_id ρ ρ'
  have hinv : ∀ (p : G ⟶ G₀) [IsMonHom p] (ρ : D₀.toPre.X →+ D.toPre.X), TorMatch U₀ U (RingHom.id V₁) p.left ρ →
      TorMatch U₀ U (RingHom.id V₁) (p⁻¹).left (-ρ) := by
    intro p _ ρ hp
    obtain ⟨ρ', hρ'⟩ := GlobalTheory.Poinc.HomTor.exists_torMatch V₁ hB G₀ hG₀ D₀ A₀ U₀ G hG D P U p⁻¹ inferInstance
    have h1 := hmul p p⁻¹ ρ ρ' hp hρ'
    rw [mul_inv_cancel] at h1
    have h2 : ρ + ρ' = 0 := huniq _ _ _ h1 hone
    have h3 : ρ' = -ρ := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact h2
    rwa [← h3]
  have hnpow : ∀ (p : G ⟶ G₀) (ρ : D₀.toPre.X →+ D.toPre.X) (n : ℕ), TorMatch U₀ U (RingHom.id V₁) p.left ρ →
      TorMatch U₀ U (RingHom.id V₁) (p ^ n).left (n • ρ) := by
    intro p ρ n hp
    induction n with
    | zero => rw [pow_zero, zero_smul]; exact hone
    | succ n ih => rw [pow_succ, succ_nsmul]; exact hmul _ _ _ _ ih hp
  have hzpow : ∀ (p : G ⟶ G₀) [IsMonHom p] (ρ : D₀.toPre.X →+ D.toPre.X) (k : ℤ),
      TorMatch U₀ U (RingHom.id V₁) p.left ρ → TorMatch U₀ U (RingHom.id V₁) (p ^ k).left (k • ρ) := by
    intro p _ ρ k hp
    cases k with
    | ofNat n => rw [Int.ofNat_eq_coe, zpow_natCast, natCast_zsmul]; exact hnpow p ρ n hp
    | negSucc n =>
      rw [zpow_negSucc, ← inv_pow, negSucc_zsmul, ← smul_neg]
      exact hnpow _ _ (n + 1) (hinv p ρ hp)
  have hprod : ∀ (n : ℕ) (g : Fin n → (G ⟶ G₀)) (r : Fin n → (D₀.toPre.X →+ D.toPre.X)),
      (∀ i, TorMatch U₀ U (RingHom.id V₁) (g i).left (r i)) →
      TorMatch U₀ U (RingHom.id V₁) (List.ofFn g).prod.left (∑ i, r i) := by
    intro n
    induction n with
    | zero => intro g r _; rw [List.ofFn_zero, List.prod_nil, Finset.univ_eq_empty, Finset.sum_empty]; exact hone
    | succ n ih =>
      intro g r h
      rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
      exact hmul _ _ _ _ (h 0) (ih _ _ fun i => h i.succ)
  have hright : TorMatch U₀ U (RingHom.id V₁) (f ≫ q u).left (∑ v, a u v • c v) := by
    rw [hfq u]
    exact hprod 8 _ _ fun v => haveI := hq v; hzpow (q v) (c v) (a u v) (hc v)
  have hleft := GlobalTheory.Poinc.Eq8.torMatch_comp V₁ hB G₀ hG₀ D₀ A₀ U₀ V₁ hB G hG D P U (RingHom.id V₁) (q u).left
    V₁ hB G hG D P U (RingHom.id V₁) f.left Function.injective_id (fun _ hk => hk) (c u) m (hc u)
    (GlobalTheory.Poinc.TorEnd.torMatch_of_endChar V₁ hB G hG D P U f hf m hm)
  rw [RingHom.id_comp, ← Over.comp_left] at hleft
  have e := huniq _ _ _ hleft hright
  have e' := DFunLike.congr_fun e χ
  simpa using e'

end GlobalTheory.Poinc.MatChar
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.ClassicalPt

theorem extend_completion : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (M : RatModel o' Ω) (x : M.Z) (R : Type) [CommRing R] (j : M.Z.presheaf.stalk x →+* R), IsCpl j → ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), y (cPt p) = x → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (ev₀ : R →+* V) (i : V →+* OO p), IsAdicComplete (maximalIdeal V) V ∧ IsLocalHom ev₀ ∧ IsLocalHom i ∧ Function.Injective i ∧ spMap (i.comp ev₀) ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y ∧ ∀ ev : R →+* OO p, spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y → ev = i.comp ev₀ := by
  intro o' Ω _ _ _ _ M x R _ j hj p _ y hy
  obtain ⟨φ, hφl, hφ, hφu⟩ := GlobalTheory.T.exists_unique_stalkHom_padicAlgClosure_valuation M.Z x p y hy
  obtain ⟨U, hU, hxU, hft⟩ := GlobalTheory.T.exists_affineOpen_finiteType_int_of_model o' Ω M x
  obtain ⟨hN, K, hK, hφK⟩ := GlobalTheory.T.stalk_noetherian_padicImage_finiteExtension M.Z U hU x hxU hft p φ
  obtain ⟨hdvr, hcpl, -⟩ := GlobalTheory.intRing_complete_dvr p K hK
  obtain ⟨e, he⟩ := hj
  let i : GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K →+* OO p :=
    RingHom.codRestrict ((algebraMap K (PadicAlgCl p)).comp (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K).subtype) (OO p) (fun v => v.2)
  let ψK : M.Z.presheaf.stalk x →+* K :=
    RingHom.codRestrict ((OO p).subtype.comp φ) K (fun a => hφK a)
  let ψ : M.Z.presheaf.stalk x →+* GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K :=
    RingHom.codRestrict ψK (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) (fun a => (φ a).2)
  have hiψ : ∀ a, i (ψ a) = φ a := fun a => rfl
  have hil : IsLocalHom i := ⟨fun v hv => by
    obtain ⟨w, hw⟩ := hv.exists_right_inv
    have hw' : algebraMap K (PadicAlgCl p) (v : K) * (w : PadicAlgCl p) = 1 :=
      congrArg Subtype.val hw
    have h0 : (v : K) ≠ 0 := by
      intro h0
      rw [h0, map_zero, zero_mul] at hw'
      exact zero_ne_one hw'
    refine isUnit_iff_exists_inv.2 ⟨⟨(v : K)⁻¹, ?_⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩
    show algebraMap K (PadicAlgCl p) (v : K)⁻¹ ∈ OO p
    rw [map_inv₀, inv_eq_of_mul_eq_one_right hw']
    exact w.2⟩
  have hψl : IsLocalHom ψ := ⟨fun a ha => hφl.map_nonunit a (by rw [← hiψ]; exact ha.map i)⟩
  haveI := hN
  haveI := hcpl
  obtain ⟨ev', hev'l, hev'⟩ := GlobalTheory.T.exists_isLocalHom_adicCompletion_extension_apply (M.Z.presheaf.stalk x) (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) ψ hψl
  have hej : ∀ a, e.symm (j a) = algebraMap _ _ a := fun a => by rw [← he a, e.symm_apply_apply]
  let ev₀ : R →+* GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K := ev'.comp e.symm.toRingHom
  have hcomp : (i.comp ev₀).comp j = φ := RingHom.ext fun a => by
    show i (ev' (e.symm (j a))) = φ a
    rw [hej, hev', hiψ]
  refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K, inferInstance, inferInstance, hdvr, ev₀, i, hcpl, ?_, hil, ?_, ?_, ?_⟩
  · refine ⟨fun r hr => ?_⟩
    have h1 := hev'l.map_nonunit _ hr
    have h2 := h1.map e.toRingHom
    simpa using h2
  · intro a b hab
    have h := congrArg Subtype.val hab
    exact Subtype.ext ((algebraMap K (PadicAlgCl p)).injective h)
  · rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp, hφ]
  · intro ev hev
    have h1 : ev.comp j = φ := hφu _ (by
      rw [← hev, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp])
    have hf : (ev.comp e.toRingHom).comp (algebraMap _ _) = φ := RingHom.ext fun a => by
      rw [← h1]; simp [he]
    have h2 := GlobalTheory.T.adicCompletion_ringHom_ext_padicAlgClosure (M.Z.presheaf.stalk x) p (ev.comp e.toRingHom) ((i.comp ev₀).comp e.toRingHom)
      (by rw [hf]; exact hφl) (fun a => by
        have := congrArg (fun F => F a) hf
        have h3 := congrArg (fun F => F a) hcomp
        simp only [RingHom.comp_apply] at this h3
        change ev (e (algebraMap _ _ a)) = i (ev₀ (e (algebraMap _ _ a)))
        rw [he, h3, ← h1]
        rfl)
    refine RingHom.ext fun r => ?_
    have := congrArg (fun F => F (e.symm r)) h2
    simpa using this

end GlobalTheory.ClassicalPt
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.isLocalHom_completedStalk_to_dvr_over_trait : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (M : RatModel o' Ω) (x : M.Z) (R : Type) [CommRing R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), IsCpl j → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V) (V' : Type) [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] (h : V →+* V') (g' : R →+* V') (ξ : Sp V ⟶ M.Z), Irreducible (h ϖ) → ξ (IsLocalRing.closedPoint V) = x → spMap g' ≫ (spMap j ≫ M.Z.fromSpecStalk x) = spMap h ≫ ξ → IsLocalHom g' := by
  first | exact @GlobalTheory.Poinc.TraitLocal.isLocalHom_of_square | exact GlobalTheory.Poinc.TraitLocal.isLocalHom_of_square | (intros; apply GlobalTheory.Poinc.TraitLocal.isLocalHom_of_square <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.OpenLev

theorem exists_open_finite : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (β : cycAway n →+* o) (S : ThetaSys o Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X), SysAt F W β S ρ u → ∀ (Y X M : RatModel o Ω) (q : Y.Z ⟶ F.X) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (fM : M.Z ⟶ X.Z) (Xab : X.Z.Opens) (Zh : ZHOut ρ M U₀ EE) (d : Y.Z ⟶ X.Z), LevAt F β u Y q → MinorAt S X M U₀ EE fM Xab → (abLocus Zh.G : Set M.Z) = fM ⁻¹' (Xab : Set X.Z) → X.IsHom Y (AlgHom.id o Ω) d → IsOpenImmersion d → ∃ (U : M.Z.Opens) (c : U.toScheme ⟶ F.X), OpenAt F β u M U c ∧ (U : Set M.Z) ⊆ abLocus Zh.G := by
  intro g n _ _ _ F W _ o Ω _ _ _ _ β S ρ u hsys Y X M q U₀ EE fM Xab Zh d hlev hmin hab hd hdo
  obtain ⟨-, -, -, h0, -, hfM, -, hiso⟩ := hmin
  have hsurj := GlobalTheory.T.surjective_functionFieldModelHom_of_projective o Ω X M fM hfM h0.proj
  have hrange : Set.range d ⊆ Xab := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨z, hz⟩ := hsurj (d y)
    obtain ⟨V, _, _, _, ξ, τ, κ, hzξ, h1, h2⟩ := GlobalTheory.T.exists_dvr_centred_point_generic_both_models o Ω Y X M fM d hfM hd hdo z ⟨y, hz.symm⟩
    have hzab : z ∈ (abLocus Zh.G : Set M.Z) :=
      GlobalTheory.T.range_subset_abelianLocus_of_levelTrait g n F W o Ω β S ρ u hsys Y M q U₀ EE Zh hlev h0 V ξ τ κ h1 h2 hzξ
    rw [hab] at hzab
    show d y ∈ (Xab : Set X.Z)
    rw [← hz]
    exact hzab
  obtain ⟨U, c, hc, hU⟩ := GlobalTheory.T.exists_open_finite_onto_of_levelCover g n F o Ω β S u Y X M q fM Xab d hlev hfM hiso hd hdo hrange
  exact ⟨U, c, hc, hab ▸ hU⟩

end GlobalTheory.OpenLev
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc

theorem exists_deep_level : ∀ {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z} (X₁ : Setup F W i) (K : ℕ), 0 < K → IsUnit (K : X₁.o₁) → ∃ (o₂ Ω₂ : Type) (_ : CommRing o₂) (_ : Field Ω₂) (_ : Algebra o₂ Ω₂) (_ : ArithBase o₂ Ω₂) (_ : Algebra X₁.Ω₁ Ω₂) (κ : X₁.o₁ →+* o₂), FiniteDimensional X₁.Ω₁ Ω₂ ∧ IsGalois X₁.Ω₁ Ω₂ ∧ κ.Finite ∧ (algebraMap o₂ Ω₂).comp κ = (algebraMap X₁.Ω₁ Ω₂).comp (algebraMap X₁.o₁ X₁.Ω₁) ∧ ∃ (R : Subalgebra o₂ Ω₂) (h : X₁.S.R →+* R) (P : PolAV (Sp R)) (ψ : P.A.left ⟶ X₁.ρ.P.A.left) (ze : o₂ˣ), R.FG ∧ (∀ x : Ω₂, ∃ a ∈ R, ∃ b ∈ R, x = a / b) ∧ (∀ a, ((h a : R) : Ω₂) = algebraMap X₁.Ω₁ Ω₂ a) ∧ P.g = X₁.ρ.P.g ∧ IsGrpPullback P.A X₁.ρ.P.A (spMap h) ψ ∧ LBIso P.L (X₁.ρ.P.L.pull ψ) ∧ Nonempty (Out.Level P K (unitOn ((Units.map (algebraMap o₂ R : o₂ →* R)) ze))) := by
  intro g n F W Z i X₁ K hK hKu
  haveI : CharZero X₁.Ω₁ := ArithBase.char X₁.o₁
  obtain ⟨Ω₂, _, _, Q, φ, ζ, hfd, hgal, hζ, hg, hpb, hlb, hlev⟩ := GlobalTheory.T.exists_symplecticLevel_genericFibre_galoisExtension X₁.S.R.val.toRingHom X₁.ρ.P K hK
  obtain ⟨o₂, _, _, _, κ, ze, hfin, hcomp, hze⟩ := GlobalTheory.T.exists_arithBase_finite_containing_rootOfUnity (o₁ := X₁.o₁) (Ω₁ := X₁.Ω₁) Ω₂ K ζ hK hζ
  have hKu₂ : IsUnit (K : o₂) := by simpa using hKu.map κ
  have hlev' : Nonempty (Out.Level Q K (unitOn (Units.map (algebraMap o₂ Ω₂ : o₂ →* Ω₂) ze))) := by rw [hze]; exact hlev
  obtain ⟨R, h, P, ψ, hR, hfr, hh, hPg, hPpb, hPlb, hPlev⟩ := GlobalTheory.T.levelStructure_genericFibre_spreads_fg_subalgebra X₁.S.R X₁.ρ.P κ Q φ K ze X₁.S.fg X₁.S.frac hfd hcomp hKu₂ hg hpb hlb hlev'
  exact ⟨o₂, Ω₂, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, κ, hfd, hgal, hfin, hcomp, R, h, P, ψ, ze, hR, hfr, hh, hPg, hPpb, hPlb, hPlev⟩

end GlobalTheory.Poinc
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.polarized_abelian_variety_pullback_affine_open : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (U : X₁.M.Z.Opens) (P' : PolAV (Sp (X₁.M.ringOn U))) (P₀ : PolAV (Sp X₁.Ω₁)) (a : P₀.A.left ⟶ X₁.ρ.P.A.left) (a' : P₀.A.left ⟶ P'.A.left), IsAffineOpen U → (U : Set X₁.M.Z).Nonempty → IsGrpPullback P₀.A X₁.ρ.P.A (spMap X₁.S.R.val.toRingHom) a → IsGrpPullback P₀.A P'.A (spMap (X₁.M.ringOn U).val.toRingHom) a' → LBIso P₀.L (X₁.ρ.P.L.pull a) → LBIso P₀.L (P'.L.pull a') → ∃ pt' : X₁.S.Gam → (baseOver (Sp (X₁.M.ringOn U)) ⟶ P'.A), (∀ x y, pt' (x + y) = pt' x * pt' y) ∧ (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp (X₁.M.ringOn U)) (z : Over.mk x ⟶ P'.A), z ^ (X₁.S.r * X₁.S.N) = 1 → ∃! c, (Over.homMk x (by simp) : Over.mk x ⟶ baseOver (Sp (X₁.M.ringOn U))) ≫ pt' c = z) ∧ (∀ x y (c : (X₁.M.ringOn U)ˣ), (c : (X₁.M.ringOn U)) = algebraMap X₁.o₁ (X₁.M.ringOn U) (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (eStd X₁.S.g _ x y).val)) → WeilIs P'.A P'.L (X₁.S.r * X₁.S.N : ℕ) (pt' x) (pt' y) (unitOn c)) ∧ (∀ x, ∃ w0 : Sp X₁.Ω₁ ⟶ P₀.A.left, w0 ≫ a = spMap X₁.S.R.val.toRingHom ≫ (X₁.ρ.pt x).left ∧ w0 ≫ a' = spMap (X₁.M.ringOn U).val.toRingHom ≫ (pt' x).left) := by
  first | exact @GlobalTheory.Poinc.TorsExtend.exists_labelled_on_chart | exact GlobalTheory.Poinc.TorsExtend.exists_labelled_on_chart | (intros; apply GlobalTheory.Poinc.TorsExtend.exists_labelled_on_chart <;> assumption)
end
