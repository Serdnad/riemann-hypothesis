module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle364
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle005
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle469
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle871
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1541
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle872
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle894
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle369
public import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle783
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle013
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1483
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle917
public import Development.AbelianVarietyTheory.Definitions.Divisors.NAInterSupSSubset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1146
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermAutomorphicFormIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1489
import GroundTheory.AutomorphicForms.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1535
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1536
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceTensorRatFiniteAlgebraModuleTopology
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1538
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle042
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Mathlib.Topology.Compactness.Paracompact
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

theorem GlobalTheory.ClassSum.sum_covolume_le : GlobalTheory.Published.TamagawaSpecialUnitary → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M m : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (Ψ : Finset (E →+* ℂ)) (X : Fin m → Data E r) (g : Fin m → Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)) (x0 : ∀ i, Frame (X i).Ψ r) (S : Finset (Fin m)) (g0 : Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)), 2 ≤ r → 3 ≤ M → Unr E → SelfDualLat G Λ → IsUA (IsCMField.complexConj E) G g0 → (∀ i, IsUA (IsCMField.complexConj E) G (g i)) → (∀ i ∈ S, TEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M g0.det (g i).det) → (∀ i ∈ S, ∀ j ∈ S, UEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M (g i) (g j) → i = j) → (∀ i ∈ S, (X i).Gm = G ∧ (X i).Ψ = Ψ ∧ ((X i).Λ : Set (Fin r → E)) = latOf (maximalRealSubfield E) (g i) (Λ : Set (Fin r → E)) ∧ (∀ γ, γ ∈ (X i).Γ ↔ IsUStab G (X i).Λ γ ∧ ∀ x ∈ (X i).Λ, ∃ y ∈ (X i).Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ x - x = M • y) ∧ IsOrth (X i) (x0 i)) → ∑ i ∈ S, covolume (inReal (X i).Ψ (X i).Gm (X i).Γ) (realSU (X i).Ψ (X i).Gm) (riemHaar (X i).Ψ (X i).Gm (x0 i)) ≤ ENNReal.ofReal ((M : ℝ) ^ (2 * fdeg E * r ^ 2) * rdE E ^ ((fdeg E : ℝ) * ((r : ℝ) ^ 2 - 1) / 2) * (Real.sqrt r * ∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i) ^ fdeg E) := by
  intro hP E _ _ _ r M m G Λ Ψ X g x0 S g0 hr hM hU hΛ hg0 hg hT hUE hX
  classical
  rcases S.eq_empty_or_nonempty with hS | ⟨i0, hi0⟩
  · subst hS; simp
  obtain ⟨hG0, hΨ0, -, -, hO0⟩ := hX i0 hi0
  subst hG0
  subst hΨ0
  obtain ⟨L, hLset, hLhat, hL⟩ := GlobalTheory.T.self_dual_lattice_real_completion E r (X i0).Gm Λ g0 hΛ hg0
  obtain ⟨γ, s, hγs, hpair⟩ := GlobalTheory.T.self_dual_lattice_congruence_subgroups E r M m (X i0).Gm Λ L g g0 S (fun i => (X i).Γ) (fun i => (X i).Λ)
    (by omega) hΛ hg0 hLset hLhat hg hT (fun i hi => ⟨(hX i hi).2.2.1, (hX i hi).2.2.2.1⟩)
  have hherm : ∀ a b, cc ((X i0).Gm a b) = (X i0).Gm b a := (X i0).Gm_herm
  have tr : ∀ (Ψ1 : Finset (E →+* ℂ)) (G1 : Matrix (Fin r) (Fin r) E) (x1 : Frame Ψ1 r) (p1 : ℕ)
      (H : Subgroup (GL (Fin r) E)), Ψ1 = (X i0).Ψ → G1 = (X i0).Gm →
      (∀ τ : Ψ1, gram τ.1 G1 (mat x1 τ) = Matrix.diagonal fun a : Fin r => ((sgn p1 (a : ℕ) : ℝ) : ℂ)) →
      covolume (inReal Ψ1 G1 H) (realSU Ψ1 G1) (riemHaar Ψ1 G1 x1) =
        covolume (inReal (X i0).Ψ (X i0).Gm H) (realSU (X i0).Ψ (X i0).Gm) (riemHaar (X i0).Ψ (X i0).Gm (x0 i0)) := by
    intro Ψ1 G1 x1 p1 H h1 h2 h3
    subst h1 h2
    rw [GlobalTheory.T.riemannianHaar_independent_of_orthonormal_frame E r p1 (X i0).p0 _ _ x1 (x0 i0) hherm h3 hO0]
  set Δ : Fin m → Subgroup (GL (Fin r) E) := fun i => ((X i).Γ).map (MulAut.conj (γ i)⁻¹).toMonoidHom with hΔ
  have hback : ∀ i, (Δ i).map (MulAut.conj (γ i)).toMonoidHom = (X i).Γ := by
    intro i
    rw [hΔ, Subgroup.map_map]
    have : (MulAut.conj (γ i)).toMonoidHom.comp (MulAut.conj (γ i)⁻¹).toMonoidHom = MonoidHom.id _ := by
      ext δ : 1
      simp [mul_assoc]
    rw [this, Subgroup.map_id]
  have hterm : ∀ i ∈ S, covolume (inReal (X i).Ψ (X i).Gm (X i).Γ) (realSU (X i).Ψ (X i).Gm)
      (riemHaar (X i).Ψ (X i).Gm (x0 i)) =
      covolume (inReal (X i0).Ψ (X i0).Gm (Δ i)) (realSU (X i0).Ψ (X i0).Gm) (riemHaar (X i0).Ψ (X i0).Gm (x0 i0)) := by
    intro i hi
    obtain ⟨hGi, hΨi, -, -, hOi⟩ := hX i hi
    rw [tr (X i).Ψ (X i).Gm (x0 i) (X i).p0 (X i).Γ hΨi hGi hOi, ← hback i]
    exact GlobalTheory.T.hermitian_gram_diagonal_signature_unitary E r (X i0).p0 (X i0).Ψ (X i0).Gm (x0 i0) (γ i) (Δ i) hherm hO0 (hγs i hi).1
  obtain ⟨J, t, ht, hcount⟩ := GlobalTheory.T.signature_unitary_lattice_family E r M (X i0).p0 (X i0).Gm L (X i0).Ψ (x0 i0) (Fin m) S s Δ hr
    (by omega) hL (X i0).cmType hO0 (fun i hi => (hγs i hi).2.1)
    (fun i hi j hj h => hUE i hi j hj (hpair i hi j hj h)) (fun i hi => (hγs i hi).2.2)
  have hV := GlobalTheory.T.real_unitary_covolume_sum hP E r (X i0) L (x0 i0) J t hr hU hL hO0 ht
  rw [Finset.sum_congr rfl hterm]
  refine hcount.trans ?_
  calc (M : ℝ≥0∞) ^ (2 * fdeg E * r ^ 2) * ∑' j, covolume (inReal (X i0).Ψ (X i0).Gm (ratStab (X i0).Gm (L : Set (Fin r → E)) (t j))) (realSU (X i0).Ψ (X i0).Gm) (riemHaar (X i0).Ψ (X i0).Gm (x0 i0))
      ≤ (M : ℝ≥0∞) ^ (2 * fdeg E * r ^ 2) * ENNReal.ofReal (rdE E ^ ((fdeg E : ℝ) * ((r : ℝ) ^ 2 - 1) / 2) * (Real.sqrt r * ∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i) ^ fdeg E) := by
        gcongr
    _ = _ := by
        rw [mul_assoc ((M : ℝ) ^ (2 * fdeg E * r ^ 2)), ENNReal.ofReal_mul (p := (M : ℝ) ^ (2 * fdeg E * r ^ 2)) (by positivity),
          ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
end

section

open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

noncomputable section
namespace GlobalTheory.RealWeilFinFix

theorem actOF_fin : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (nS nT : ℕ)
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (g : GAF σ JS) (h : GAF σ JT),
      g ∈ GlobalTheory.WeilPartsF.GinfCF σ JS → h ∈ GlobalTheory.WeilPartsF.GinfCF σ JT → ∀ u : WOF F E nS nT, u.map (infPartF F E) = 0 →
        actOF σ JS JT g h u = u := by
  intro F E _ _ _ _ _ σ nS nT JS JT g h hg hh u hu
  have h1 : (mtF σ JT h).map (finPartF F E) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 hh)
  have h2 : (mtF σ JS g⁻¹).map (finPartF F E) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 (inv_mem hg))
  have h3 : (actOF σ JS JT g h u).map (finPartF F E) = u.map (finPartF F E) := by
    unfold actOF
    rw [Matrix.map_mul, Matrix.map_mul, h1, h2, Matrix.one_mul, Matrix.mul_one]
  have h4 : (actOF σ JS JT g h u).map (infPartF F E) = u.map (infPartF F E) := by
    unfold actOF
    rw [Matrix.map_mul, Matrix.map_mul, hu, Matrix.mul_zero, Matrix.zero_mul]
  ext i j
  have k3 : finPartF F E (actOF σ JS JT g h u i j) = finPartF F E (u i j) := congrFun (congrFun h3 i) j
  have k4 : infPartF F E (actOF σ JS JT g h u i j) = infPartF F E (u i j) := congrFun (congrFun h4 i) j
  rw [← Formalism.L2.Fam.ThC.pairE_eta (actOF σ JS JT g h u i j), ← Formalism.L2.Fam.ThC.pairE_eta (u i j)]
  exact congrArg₂ Formalism.L2.Fam.ThC.pairE k4 k3

end GlobalTheory.RealWeilFinFix
end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GeoActCompare

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
  Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke
open GlobalTheory.FormTies (levFull)
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Rel

open CategoryTheory MonObj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

end Rel

section Half

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}

theorem exists_half (a : Dw.La) : ∃ b ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La),
    (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ b = (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ a := by
  have h : a ∈ (l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) • (⊤ : Submodule (𝓞 E) Dw.La) := by
    rw [l.coprime, Submodule.top_smul]; trivial
  rw [Submodule.sup_smul] at h
  obtain ⟨x, hx, b, hb, rfl⟩ := Submodule.mem_sup.1 h
  refine ⟨b, hb, ?_⟩
  rw [map_add (f := _), show (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ x = 0 from (Submodule.Quotient.mk_eq_zero _).2 hx, zero_add]

theorem map_mem_smul_top {I : Ideal (𝓞 E)} (f : Dw.La →ₗ[𝓞 E] Dw.La) {a : Dw.La}
    (ha : a ∈ I • (⊤ : Submodule (𝓞 E) Dw.La)) : f a ∈ I • (⊤ : Submodule (𝓞 E) Dw.La) := by
  have h := Submodule.mem_map_of_mem (f := f) ha
  rw [Submodule.map_smul''] at h
  exact Submodule.smul_mono le_rfl le_top h

theorem half_ne_bot (l : Level H) : l.Mb ≠ ⊥ := by
  intro h
  have h1 := l.prod
  rw [h, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot] at h1
  have := l.three_le
  have h2 : l.M = 0 := by exact_mod_cast h1
  omega

theorem graph_iff {r : ℕ} (φ : LaMod Dw l ≃ₗ[𝓞 E] (Fin r → 𝓞 E ⧸ l.Mb)) (Y : Matrix (Fin r) (Fin r) (𝓞 E ⧸ l.Mb))
    (C : Dw.La → Dw.La → Prop)
    (hC : ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La),
      ∀ a' ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La), C a a' ↔
        φ ((l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ a') = Y.mulVec (φ ((l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ a)))
    (γ : LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l) :
    (∀ q, φ (γ q) = Y.mulVec (φ q)) ↔
      ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La),
      ∀ a' ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La),
        (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ a' = γ ((l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ a) → C a a' := by
  constructor
  · intro hg a ha a' ha' e
    rw [hC a ha a' ha', e, hg]
  · intro hg q
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ q
    obtain ⟨a, ha, e⟩ := exists_half (l := l) x
    have ha' := map_mem_smul_top (liftLa γ) ha
    rw [← e, ← liftLa_spec]
    exact (hC a ha _ ha').1 (hg a ha _ ha' (liftLa_spec _ a))

end Half

theorem exists_coord_of {O S La : Type} [CommRing O] [CommRing S] [AddCommGroup La] [Module O La] (o : O →+* S)
    {I J : Ideal O} {M r : ℕ} (hIJ : I * J = Ideal.span {(M : O)}) (hco : I ⊔ J = ⊤) (π : S →+* O ⧸ I)
    (hπ : ∀ a, π (o a) = Ideal.Quotient.mk I a) (hπ0 : ∀ s, π s = 0 ↔ s ∈ I.map o) (ρ : La →+ (Fin r → S))
    (hlin : ∀ (b : O) (a : La), ρ (b • a) = o b • ρ a)
    (hsur : ∀ s : Fin r → S, ∃ (a : La) (s' : Fin r → S), s = ρ a + M • s')
    (hker : ∀ a : La, (∀ i, ρ a i ∈ I.map o) → a ∈ I • (⊤ : Submodule O La)) :
    ∃ φ : (La ⧸ (I • (⊤ : Submodule O La))) ≃ₗ[O] (Fin r → O ⧸ I), ∀ y : Matrix (Fin r) (Fin r) S,
      ∀ a ∈ J • (⊤ : Submodule O La), ∀ a' ∈ J • (⊤ : Submodule O La),
        (∃ s : Fin r → S, y.mulVec (ρ a) - ρ a' = M • s) ↔
          φ ((I • (⊤ : Submodule O La)).mkQ a') = (y.map π).mulVec (φ ((I • (⊤ : Submodule O La)).mkQ a)) := by
  have hMb : (M : O) ∈ I :=
    Ideal.mul_le_left (I := I) (J := J) (by rw [hIJ]; exact Ideal.mem_span_singleton_self _)
  have hπM : ∀ s : S, π (M • s) = 0 := fun s => (hπ0 _).2 (by
    rw [nsmul_eq_mul, ← map_natCast o]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hMb))
  have hmem : ∀ K : Ideal O, ∀ a ∈ K • (⊤ : Submodule O La), ∀ i, ρ a i ∈ K.map o := fun K a ha i => by
    refine Submodule.smul_induction_on (p := fun a => ρ a i ∈ K.map o) ha ?_ ?_
    · intro b hb x _
      rw [hlin]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hb)
    · intro x y hx hy
      rw [map_add (f := _)]
      exact add_mem hx hy
  let f : La →ₗ[O] (Fin r → O ⧸ I) :=
    { toFun := fun a i => π (ρ a i)
      map_add' := fun a b => funext fun i => by simp
      map_smul' := fun b a => funext fun i => by
        rw [hlin, Pi.smul_apply, smul_eq_mul, map_mul, hπ]
        rfl }
  have hk : LinearMap.ker f = I • (⊤ : Submodule O La) := by
    ext a
    rw [LinearMap.mem_ker]
    exact ⟨fun h => hker a fun i => (hπ0 _).1 (congrFun h i), fun h => funext fun i => (hπ0 _).2 (hmem _ a h i)⟩
  have hs : Function.Surjective f := fun x => by
    choose b hb using fun i => Ideal.Quotient.mk_surjective (x i)
    obtain ⟨a, s', e⟩ := hsur fun i => o (b i)
    refine ⟨a, funext fun i => ?_⟩
    have := congrArg π (congrFun e i)
    rw [Pi.add_apply, map_add (f := _), Pi.smul_apply, hπM, add_zero, hπ, hb] at this
    exact this.symm
  refine ⟨(Submodule.quotEquivOfEq _ _ hk.symm).trans (f.quotKerEquivOfSurjective hs), fun y a ha a' ha' => ?_⟩
  change _ ↔ f a' = (y.map π).mulVec (f a)
  have hv : ∀ i, ((y.map π).mulVec (f a)) i = π (y.mulVec (ρ a) i) := fun i =>
    (RingHom.map_mulVec π y (ρ a) i).symm
  constructor
  · rintro ⟨s, e⟩
    funext i
    have := congrArg π (congrFun e i)
    rw [Pi.sub_apply, map_sub, Pi.smul_apply, hπM, sub_eq_zero] at this
    rw [hv]
    exact this.symm
  · intro e
    have h1 : ∀ i, (y.mulVec (ρ a) - ρ a') i ∈ Ideal.span {(M : S)} := fun i => by
      have hb : (y.mulVec (ρ a) - ρ a') i ∈ I.map o := by
        rw [← hπ0, Pi.sub_apply, map_sub, sub_eq_zero, ← hv, ← e]
        rfl
      have hc : (y.mulVec (ρ a) - ρ a') i ∈ J.map o := by
        refine sub_mem ?_ (hmem _ a' ha' i)
        exact Ideal.sum_mem _ (t := Finset.univ) (f := fun k => y i k * ρ a k) fun k _ =>
          Ideal.mul_mem_left _ _ (hmem _ a ha k)
      have hco' : I.map o ⊔ J.map o = ⊤ := by rw [← Ideal.map_sup, hco, Ideal.map_top]
      have hi := Submodule.mem_inf.2 ⟨hb, hc⟩
      rwa [← Ideal.mul_eq_inf_of_coprime hco', ← Ideal.map_mul, hIJ, Ideal.map_span, Set.image_singleton,
        map_natCast] at hi
    choose s hs using fun i => Ideal.mem_span_singleton'.1 (h1 i)
    exact ⟨s, funext fun i => by rw [← hs i, Pi.smul_apply, nsmul_eq_mul, mul_comm]⟩

variable {D : D7}

section Dict

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}

def Cong (V : HSp D) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (M : ℕ) (κ : GA D V) (a a' : Dw.La) : Prop :=
  ∃ w ∈ latGHat V 1, (finHom V κ).1.mulVec (finVec V (ι a)) - finVec V (ι a') = M • w



theorem exists_coord (l : Level H) (V : HSp D) {r : ℕ} (hr : V.rank = r) (β : GL (Fin r) (EAf D))
    (hβ : LatticeBasisLifts.IsLatBasis V hr β) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (hι : LatEmb V ι) :
    ∃ φ : LaMod Dw l ≃ₗ[𝓞 D.host.E] (Fin r → 𝓞 D.host.E ⧸ l.Mb),
      ∀ (κ : GA D V) (h : LatticeBasisLifts.finR V hr κ ∈ Formalism.L2.DIV.St β),
      ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∀ a' ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
        Cong V ι l.M κ a a' ↔
          φ ((l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)).mkQ a') =
            ((Formalism.L2.DIV.pullFr β ⟨_, h⟩).1.map (resI D.host.F l.Mb (half_ne_bot l))).mulVec
              (φ ((l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)).mkQ a)) := by
  obtain ⟨ρ, hlin, hsur, hker, hcong⟩ := GlobalTheory.T.exists_integral_adelic_coordinates_lattice_mod D V r hr β hβ Dw.La ι hι l.M (by have := l.three_le; omega)
  obtain ⟨φ, hφ⟩ := exists_coord_of (Formalism.L2.DIV.oToS D.host.F D.host.E) l.prod l.coprime
    (resI D.host.F l.Mb (half_ne_bot l)) (resI_oToS _ _) (resI_eq_zero_iff _ _) ρ hlin hsur (hker _ _ l.prod)
  refine ⟨φ, fun κ h a ha a' ha' => ?_⟩
  have h1 := hcong κ _ (Formalism.L2.DIV.frGL_pullFr β ⟨_, h⟩).symm a a'
  have h2 := hφ (Formalism.L2.DIV.pullFr β ⟨_, h⟩).1 a ha a' ha'
  have h3 := h1.trans h2
  exact h3

end Dict

end GlobalTheory.GeoActCompare
end
end

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory Topology

namespace GlobalTheory.JSW.MirSemi

open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem whit_smul_fun (c : ℂ) (F : GA E a → ℂ) (g : GA E a) : whit (c • F) g = c * whit F g := by
  unfold whit whittaker
  rw [← integral_const_mul]
  congr 1
  funext X
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem whit_mul_right_fun (F : GA E a → ℂ) (g h : GA E a) : whit F (g * h) = whit (fun z => F (z * h)) g := by
  simp only [whit, whittaker, mul_assoc]

theorem continuous_heightInf : Continuous (fun y : GL (Fin a) (Cinf E) => height y) := by
  unfold height
  have h1 : Continuous fun y : GL (Fin a) (Cinf E) => toL y.val :=
    continuous_pi fun i => continuous_pi fun j => Units.continuous_val.matrix_elem i j
  have h2 : Continuous fun y : GL (Fin a) (Cinf E) => toL (y⁻¹).val :=
    continuous_pi fun i => continuous_pi fun j => Units.continuous_coe_inv.matrix_elem i j
  exact (continuous_const.add h1.norm).add h2.norm

theorem height_pos_inf (y : GL (Fin a) (Cinf E)) : 0 < height y := by
  unfold height; positivity

theorem whit_infGL_growth {F : GA E a → ℂ} (hc : Continuous F)
    (hg : ∀ K : Set (GA E a), IsCompact K → ∃ (C : ℝ) (N : ℕ), ∀ g ∈ K, ∀ y : GL (Fin a) (Cinf E),
      ‖F (g * infGL E a y)‖ ≤ C * height y ^ N) (g : GA E a) :
    Continuous (fun y : GL (Fin a) (Cinf E) => whit F (g * infGL E a y)) ∧
      ∃ (C : ℝ) (N : ℕ), ∀ y, ‖whit F (g * infGL E a y)‖ ≤ C * height y ^ N := by
  set K : Set (GA E a) := (fun X => uGL X * g) '' closure (vecDomain E (Pos a)) with hKdef
  have hK : IsCompact K := isCompact_closure_vecDomain.image (continuous_uGL.mul continuous_const)
  obtain ⟨C, N, hC⟩ := hg K hK
  set f : GL (Fin a) (Cinf E) → (Pos a → Ad E) → ℂ := fun y X =>
    F (uGL X * (g * infGL E a y)) * (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) with hfdef
  have hwf : ∀ y, whit F (g * infGL E a y) = ∫ X in vecDomain E (Pos a), f y X ∂vecMeasure E (Pos a) :=
    fun y => rfl
  have hb : ∀ y, ∀ X ∈ vecDomain E (Pos a), ‖f y X‖ ≤ C * height y ^ N := by
    intro y X hX
    simp only [hfdef]
    rw [norm_mul, Circle.norm_coe, mul_one, ← mul_assoc]
    exact hC _ ⟨X, subset_closure hX, rfl⟩ y
  have hbound : ∀ y, ‖whit F (g * infGL E a y)‖ ≤ C * height y ^ N := by
    intro y
    have h := norm_setIntegral_le_of_norm_le_const (μ := vecMeasure E (Pos a)) (s := vecDomain E (Pos a))
      (C := C * height y ^ N) (f := f y) (by rw [vecMeasure_vecDomain]; exact ENNReal.one_lt_top) (hb y)
    rwa [measureReal_def, vecMeasure_vecDomain, ENNReal.toReal_one, mul_one, ← hwf] at h
  refine ⟨?_, C, N, hbound⟩
  haveI : IsFiniteMeasure ((vecMeasure E (Pos a)).restrict (vecDomain E (Pos a))) :=
    ⟨by rw [Measure.restrict_apply_univ, vecMeasure_vecDomain]; exact ENNReal.one_lt_top⟩
  have hchar : Continuous fun X : Pos a → Ad E => (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) :=
    continuous_subtype_val.comp (GroundTheory.Global.continuous_adelicChar.comp (continuous_supSum 0).neg)
  have hfc : ∀ y, Continuous (f y) := fun y =>
    (hc.comp (continuous_uGL.mul continuous_const)).mul hchar
  haveI : FirstCountableTopology (MulOpposite (Matrix (Fin a) (Fin a) (Cinf E))) :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin a) (Fin a) (Cinf E))).symm.isInducing.firstCountableTopology
  haveI : FirstCountableTopology (GL (Fin a) (Cinf E)) :=
    Units.isEmbedding_embedProduct.isInducing.firstCountableTopology
  rw [continuous_iff_continuousAt]
  intro y₀
  have hev : ∀ᶠ y in 𝓝 y₀, height y < height y₀ + 1 :=
    continuous_heightInf.continuousAt.eventually (gt_mem_nhds (lt_add_one _))
  simp only [hwf]
  refine continuousAt_of_dominated (bound := fun _ => max C 0 * (height y₀ + 1) ^ N) ?_ ?_ (integrable_const _) ?_
  · exact Filter.Eventually.of_forall fun y => (hfc y).aestronglyMeasurable
  · filter_upwards [hev] with y hy
    refine ae_restrict_of_forall_mem measurableSet_vecDomain fun X hX => ?_
    calc ‖f y X‖ ≤ C * height y ^ N := hb y X hX
      _ ≤ max C 0 * height y ^ N :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (height_pos_inf y).le _)
      _ ≤ max C 0 * (height y₀ + 1) ^ N :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (height_pos_inf y).le hy.le _) (le_max_right _ _)
  · refine Filter.Eventually.of_forall fun X => ?_
    have : Continuous fun y : GL (Fin a) (Cinf E) => f y X :=
      (hc.comp (continuous_const.mul (continuous_const.mul GlobalTheory.ConstTermSmooth.continuous_infGL))).mul
        continuous_const
    exact this.continuousAt

end GlobalTheory.JSW.MirSemi


open GlobalTheory.JSW.MirSemi in
theorem GlobalTheory.JSW.MirSemi.whitSpace_exists : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (π : CuspSub E (m + 1)) (φ : Sm E (m + 1)), φ ∈ π.V → ∃ 𝒲 : Submodule ℂ (GA E (m + 1) → ℂ), GlobalTheory.JSW.whit φ.1 ∈ 𝒲 ∧ (∀ W ∈ 𝒲, ∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) ∧ (∀ W ∈ 𝒲, ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, (fun g => W (g * h)) ∈ 𝒲) ∧ (∀ W ∈ 𝒲, ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin (m + 1)) (Cinf E)), GlobalTheory.JSW.IsRapidInf ν k γ → GlobalTheory.JSW.kerInf ν k γ W ∈ 𝒲) ∧ (∀ W ∈ 𝒲, ∀ g, Continuous (fun y : GL (Fin (m + 1)) (Cinf E) => W (g * infGL E (m + 1) y)) ∧ ∃ (C : ℝ) (N : ℕ), ∀ y, ‖W (g * infGL E (m + 1) y)‖ ≤ C * height y ^ N) ∧ (∀ W ∈ 𝒲, ∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, W (g * finGL E (m + 1) u) = W g) ∧ ∀ W ∈ 𝒲, ∃ F ∈ GlobalTheory.JSW.MirSemi.locSpan S φ.1, ∀ g, GlobalTheory.JSW.whit F g = W g := by
  intro E _ _ _ m S π φ hφ
  have hreg := GlobalTheory.T.cusp_form_moderate_growth_compact E (m + 1) S π φ hφ
  let 𝒲 : Submodule ℂ (GA E (m + 1) → ℂ) :=
    { carrier := {W | ∃ F ∈ locSpan S φ.1, GlobalTheory.JSW.whit F = W}
      add_mem' := by
        rintro _ _ ⟨F, hF, rfl⟩ ⟨G, hG, rfl⟩
        refine ⟨F + G, add_mem hF hG, funext fun g => ?_⟩
        have h := ((GlobalTheory.T.globalWhittakerCoefficient_linear_archimedeanKernel E (m + 1) F G (hreg F hF).1 (hreg G hG).1 (hreg F hF).2 (hreg G hG).2).1 1 g)
        simp only [one_mul] at h
        exact h
      zero_mem' := ⟨0, zero_mem _, funext fun g => by
        simpa using whit_smul_fun (0 : ℂ) (0 : GA E (m + 1) → ℂ) g⟩
      smul_mem' := by
        rintro c _ ⟨F, hF, rfl⟩
        exact ⟨c • F, Submodule.smul_mem _ c hF, funext fun g => whit_smul_fun c F g⟩ }
  refine ⟨𝒲, ⟨φ.1, self_mem_locSpan, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨F, hF, rfl⟩ u hu g
    exact GlobalTheory.JSW.WhitModel.whit_mul (hreg F hF).1
      (fun γ g => GlobalTheory.JSW.rspan_left π (locSpan_le_rspan hφ hF) γ g) hu g
  · rintro _ ⟨F, hF, rfl⟩ h hh
    exact ⟨_, rt_mem_locSpan hF hh, funext fun g => (whit_mul_right_fun F g h).symm⟩
  · rintro _ ⟨F, hF, rfl⟩ X _ ν _ k γ hk
    refine ⟨GlobalTheory.JSW.kerInf ν k γ F, kerInf_mem_locSpan hF ν hk, funext fun g => ?_⟩
    rw [(GlobalTheory.T.globalWhittakerCoefficient_linear_archimedeanKernel E (m + 1) F F (hreg F hF).1 (hreg F hF).1 (hreg F hF).2 (hreg F hF).2).2 X ν k γ hk g]
    rfl
  · rintro _ ⟨F, hF, rfl⟩ g
    exact whit_infGL_growth (hreg F hF).1 (hreg F hF).2 g
  · rintro _ ⟨F, hF, rfl⟩
    obtain ⟨U, hU, hinv⟩ := GlobalTheory.T.archimedeanKernelSpan_cuspForm_right_invariant_open E (m + 1) S π φ hφ F hF
    refine ⟨U, hU, fun u hu g => ?_⟩
    rw [whit_mul_right_fun]
    congr 1
    funext z
    exact hinv u hu z
  · rintro _ ⟨F, hF, rfl⟩
    exact ⟨F, hF, fun g => rfl⟩
end
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

theorem _root_.GlobalTheory.T.archimedeanTruncatedRow_unipotent_invariant_nonzero : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (ρ : Fin n), ∀ g ∈ levSetInf E n (ρ + 1), (∀ u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n), rowCutInf ρ ((u * g : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) = rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E))) ∧ ∀ w, ∃ j, j ≤ ρ ∧ rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E)) j w ≠ 0 := by
  first | exact @GlobalTheory.JSW.MirCinf.rowCutInf_unipB_mul_levSetInf | exact GlobalTheory.JSW.MirCinf.rowCutInf_unipB_mul_levSetInf | (intros; apply GlobalTheory.JSW.MirCinf.rowCutInf_unipB_mul_levSetInf; all_goals assumption)
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

theorem _root_.GlobalTheory.T.archimedeanSectionMatrix_invertible_level_reduction : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (ρ : Fin n) (j : InfinitePlace E → Fin n), (∀ w, j w ≤ ρ) → (∀ v : Fin n → Cinf E, (∀ w, v (j w) w ≠ 0) → IsUnit (Matrix.of (secMatInf ρ j v)) ∧ toGLInf (Matrix.of (secMatInf ρ j v)) ∈ levSetInf E n (ρ + 1)) ∧ (∀ g ∈ levSetInf E n (ρ + 1), (∀ w, rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E)) (j w) w ≠ 0) → g * (toGLInf (Matrix.of (secMatInf ρ j (rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E))))))⁻¹ ∈ levSetInf E n ρ) ∧ ∃ L : (Fin n → Cinf E) →L[ℝ] (Fin n → Fin n → Cinf E), ∀ v, secMatInf ρ j v = secMatInf ρ j 0 + L v := by
  first | (exact @GlobalTheory.JSW.MirCinf.secMatInf_main) | (exact GlobalTheory.JSW.MirCinf.secMatInf_main) | (intros; apply GlobalTheory.JSW.MirCinf.secMatInf_main  <;> assumption)
end

section

open GlobalTheory.LKTrip GlobalTheory.LKMid
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.charpoly_tensorLeftMul_conj_one_tmul : ∀ (R : Type) [CommRing R] [Algebra ℚ R] (A : Type) [Ring A] [Algebra ℚ A] [Module.Finite ℚ A] (x : (R ⊗[ℚ] A)ˣ) (y : A), (LevelExists.mulMatAlg R A ((x : R ⊗[ℚ] A) * (1 ⊗ₜ[ℚ] y) * ((x⁻¹ : (R ⊗[ℚ] A)ˣ) : R ⊗[ℚ] A))).charpoly = (LinearMap.mulLeft ℚ y).charpoly.map (algebraMap ℚ R) := by
  first | (exact @GlobalTheory.conj_one_tmul_charpoly) | (exact GlobalTheory.conj_one_tmul_charpoly) | (intros; apply GlobalTheory.conj_one_tmul_charpoly <;> assumption)
end
