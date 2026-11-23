module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle017
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle360
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle359
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle351
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle352
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle348
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle357
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle156
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.AdmissibleTwistByDet
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle047
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle133
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle337
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NontrivialOfNeBot
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2429
import Formalism.PieriBlockIdeals.BlockIdealBound5Derived

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.NfSrc

theorem upper_triangular_conj_lower_right_entry_eq {k : Type} [Field k] (B : GL (Fin 2) k) (X : Matrix (Fin 2) (Fin 2) k)
    (hB : (B : Matrix (Fin 2) (Fin 2) k) 1 0 = 0) (hX : X 1 0 = 0) :
    ((B : Matrix (Fin 2) (Fin 2) k) * X * ((B⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)) 1 1 = X 1 1 := by
  have hinv := GlobalTheory.NfEx.inv_up B hB
  have h1 : ((B⁻¹ * B : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = 1 := by simp
  have a11 := congrFun (congrFun h1 1) 1
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hinv.1, zero_mul, zero_add, Matrix.one_apply_eq] at a11
  simp only [Matrix.mul_apply, Fin.sum_univ_two, hB, hX, zero_mul, zero_add, mul_zero]
  calc _ = X 1 1 * ((B⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) 1 1 * (B : Matrix (Fin 2) (Fin 2) k) 1 1 := by ring
    _ = _ := by rw [mul_assoc, a11, mul_one]

end GlobalTheory.NfSrc

theorem GlobalTheory.Ord2.exists_nf_srcUr : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (W : R2 Ω l), l ≠ 2 → 1 ≤ e → admitted ι e W → SrcL ι e W → ∃ (S : Finset Pl) (A : ValuationSubring Ω) (W' : R2 Ω l) (g : Newform (2 * e + 1)), RepIso W W' ∧ Nf e S A W' ∧ SrcUr ι e A W' g := by
  intro l _ Ω _ _ _ ι e W hl he hW hS
  obtain ⟨⟨g0, χ, A, κ, hM0, ha0, hχ, hatt, hA, hfl, hin⟩, hne⟩ := hS
  obtain ⟨g, hg⟩ := hfl
  obtain ⟨M, hM, hMa⟩ := hW.away
  obtain ⟨S, hSa, hSu⟩ := GlobalTheory.T.unramified_of_levelAway_inertia_characters l Ω W M hM hMa
  let r : G ℚ Ω →* GL (Fin 2) (Qbar l) := (MulAut.conj g).toMonoidHom.comp W
  have hrc : Continuous r := by
    show Continuous fun s => g * W s * g⁻¹
    exact (continuous_const.mul hW.cont).mul continuous_const
  obtain ⟨E, hE, hEm⟩ := GlobalTheory.CompactRepField.exists_finiteDimensional_entries_mem l (G ℚ Ω) 2 r
    (fun i j => ((Units.continuous_val.comp hrc).matrix_elem i j))
  obtain ⟨B, hB10, hBint⟩ := GlobalTheory.T.exists_upperTriangular_conj_integral_compact l (G ℚ Ω) E r hE hrc hEm
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_coefficientRing_finiteExtension_padic l E hE
  let h : GL (Fin 2) (Qbar l) := B * g
  let W' : R2 Ω l := (MulAut.conj h).toMonoidHom.comp W
  have hh : ∀ s, W' s = h * W s * h⁻¹ := fun s => rfl
  have hW' : ∀ s, W' s = B * r s * B⁻¹ := fun s => by
    show h * W s * h⁻¹ = B * (g * W s * g⁻¹) * B⁻¹
    simp only [h, mul_inv_rev]; group
  have hiso : RepIso W W' := ⟨h, hh⟩
  have hdt : dt W' = dt W := by
    ext s
    rw [GlobalTheory.Ord2.TwDet.dt_coe, GlobalTheory.Ord2.TwDet.dt_conj W h s]
    rfl
  have hdet : ∀ s, (dt W' s : Qbar l) = (mat W' s).det := fun s => rfl
  have hker : ∀ s, W' s = 1 ↔ W s = 1 := fun s => by
    show h * W s * h⁻¹ = 1 ↔ W s = 1
    constructor
    · intro hh; rw [mul_inv_eq_one, mul_eq_left] at hh; exact hh
    · intro hh; rw [hh]; simp
  have hinv := GlobalTheory.NfEx.inv_up B hB10
  have hup : ∀ (s : G ℚ Ω) (hs : s ∈ Dec (F := ℚ) A), mat W' s 1 0 = 0 ∧ mat W' s 0 0 = (κ 0 ⟨s, hs⟩ : Qbar l) ∧
      mat W' s 1 1 = (κ 1 ⟨s, hs⟩ : Qbar l) := by
    intro s hs
    have h1 := (hg ⟨s, hs⟩).1 1 0 (by decide)
    have h2 := (hg ⟨s, hs⟩).2 0
    have h3 := (hg ⟨s, hs⟩).2 1
    have := GlobalTheory.NfEx.up2 (B : Matrix (Fin 2) (Fin 2) (Qbar l)) ((r s : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l))
      ((B⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) hB10 h1 hinv.1
    have e1 : mat W' s = (B : Matrix (Fin 2) (Fin 2) (Qbar l)) * ((r s : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) * ((B⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) := by
      simp only [mat, hW', Units.val_mul]
    refine ⟨by rw [e1]; exact this.1, ?_, ?_⟩
    · rw [e1, this.2, ← h2]
      change _ = ((r s : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) 0 0
      calc _ = (B : Matrix (Fin 2) (Fin 2) (Qbar l)) 0 0 * ((B⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) 0 0 * ((r s : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) 0 0 := by ring
        _ = _ := by rw [hinv.2, one_mul]
    · rw [e1, GlobalTheory.NfSrc.upper_triangular_conj_lower_right_entry_eq B ((r s : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) hB10 h1]
      exact h3

  have hline : ∀ (s : G ℚ Ω) (hs : s ∈ Ine (F := ℚ) A),
      mat W' s 0 0 = eps l s ^ e * (χ s : Qbar l) := by
    intro s hs
    have hd : s ∈ Dec (F := ℚ) A := Ine_le_Dec A hs
    obtain ⟨u10, u00, u11⟩ := hup s hd
    have hi := hin ⟨s, hd⟩ hs
    have hD : (dt W s : Qbar l) = mat W' s 0 0 * mat W' s 1 1 := by
      rw [← hdt, hdet, Matrix.det_fin_two, u10, mul_zero, sub_zero]
    have hdne : (dt W s : Qbar l) ≠ 0 := Units.ne_zero _
    simp only [zpow_natCast] at hi
    rw [← u11] at hi
    simp only [eps]
    calc mat W' s 0 0 = mat W' s 0 0 * (mat W' s 1 1 * (cycBar ℚ Ω l s : Qbar l) ^ e * ((dt W s : Qbar l)⁻¹ * (χ s : Qbar l))) := by
          rw [hi, mul_one]
      _ = (mat W' s 0 0 * mat W' s 1 1) * (dt W s : Qbar l)⁻¹ * ((cycBar ℚ Ω l s : Qbar l) ^ e * (χ s : Qbar l)) := by ring
      _ = _ := by rw [← hD, mul_inv_cancel₀ hdne, one_mul]
  refine ⟨S, A, W', g0, hiso, ?_, ?_⟩
  · refine
      { l_odd := hl
        e_pos := he
        cont := ?_
        int := ⟨c, fun s i j => (hc _).2 ⟨?_, ?_⟩⟩
        above := hSa
        unr := ?_
        det2 := by rw [hdt]; exact hW.det2
        odd := by rw [hdt]; exact hW.odd
        irr := GlobalTheory.T.irreducible_restriction_of_iso Ω l W W' hiso hW.irr
        atL := hA
        upper := fun s hs => (hup s hs).1
        wt := ?_
        ne := ?_ }
    · show Continuous fun s => h * W s * h⁻¹
      exact (continuous_const.mul hW.cont).mul continuous_const
    · have := (hBint s i j).1; simpa only [mat, hW'] using this
    · have := (hBint s i j).2; simpa only [mat, hW'] using this
    · intro w hw B' hB' s hs
      exact (hker s).2 (hSu w hw B' hB' hs)
    · refine ⟨l - 1, ?_, fun s hs => ?_⟩
      · have := (Fact.out : l.Prime).two_le; omega
      · rw [hline s hs, mul_pow, ← pow_mul]
        have hχ1 := GlobalTheory.T.character_pow_pred_eq_one_of_killsPrimeRoots Ω l _ χ s hχ
        rw [← Units.val_pow_eq_pow_val (χ s), hχ1, Units.val_one, mul_one]
    · obtain ⟨s, hs⟩ := hne A κ hA ⟨g, hg⟩
      refine ⟨s, s.2, ?_⟩
      rw [(hup s s.2).2.1]
      intro hh
      exact hs (Units.ext hh)
  · refine ⟨hM0, ha0, χ, hχ, ?_, ?_⟩
    · rw [hdt]
      exact SrcConj.att_conj ι g0 _ _ h (SrcConj.tw_conj W W' _ h hh) hatt
    · intro s hs
      have hd : s ∈ Dec (F := ℚ) A := Ine_le_Dec A hs
      rw [(hup s hd).2.2, hdt]
      exact hin ⟨s, hd⟩ hs

end
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology
open Matrix

noncomputable section

namespace GlobalTheory.DefU.FinCompact

theorem exists_open_compact : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ),
    ∃ K : Subgroup (finU (E := E) (n := n)), IsOpen (K : Set (finU (E := E) (n := n))) ∧ IsCompact (K : Set (finU (E := E) (n := n))) := by
  intro E _ _ _ n
  obtain ⟨U0, hU0o, hU0c⟩ := GlobalTheory.GLIntegral.exists_isOpen_isCompact E n
  let p : finU (E := E) (n := n) →* GL (Fin n) (Af E) :=
    (GeneralLinearGroup.map (pFin E)).comp ((UA E n).subtype.comp (finU (E := E) (n := n)).subtype)
  have hp : Continuous p := continuous_map_pFin.comp (continuous_subtype_val.comp continuous_subtype_val)
  let K : Subgroup (finU (E := E) (n := n)) := U0.comap p
  have hKo : IsOpen (K : Set (finU (E := E) (n := n))) := hU0o.preimage hp
  haveI := GlobalTheory.DefU.LocAdm.t2Space_adelicGL_cmField (E := E) (n := n)
  have hfc : IsClosed ((finU (E := E) (n := n) : Subgroup (UA E n)) : Set (UA E n)) := by
    haveI : T2Space (GL (Fin n) (Cinf E)) := Units.isEmbedding_embedProduct.t2Space
    have hc := GlobalTheory.CuspRep.ContAut.continuous_map_pInf E n
    exact isClosed_eq (hc.comp continuous_subtype_val) continuous_const
  have hι : Topology.IsClosedEmbedding (fun x : finU (E := E) (n := n) => ((x : UA E n) : GA E n)) :=
    GlobalTheory.DefU.LocAdm.isClosed_UA.isClosedEmbedding_subtypeVal.comp hfc.isClosedEmbedding_subtypeVal
  refine ⟨K, hKo, IsCompact.of_isClosed_subset (hι.isCompact_preimage (hU0c.image GlobalTheory.DefU.LocAdm.continuous_finGL))
    (Subgroup.isClosed_of_isOpen K hKo) fun x hx => ⟨p x, hx, ?_⟩⟩
  have h1 : GeneralLinearGroup.map (pInf E) ((x : UA E n) : GA E n) = 1 := x.2
  exact ga_ext (by rw [pInf_finGL, h1]) (by rw [pFin_finGL]; rfl)

end GlobalTheory.DefU.FinCompact
end
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology

namespace GlobalTheory.FrameAut.VecForms

theorem isAutRepU_span_values : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Type) [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S] (ρ : Representation ℂ (infU E n) S), Submodule.span ℂ (Set.range ρ) = ⊤ → ∀ M : Submodule ℂ (S →ₗ[ℂ] (UA E n → ℂ)), M ≠ ⊥ → (∀ f ∈ M, (∀ v, IsAutFormU (f v)) ∧ ∀ (x : infU E n) v, f (ρ x v) = RU E n x (f v)) → (∀ k ∈ finU (E := E) (n := n), ∀ f ∈ M, (RU E n k) ∘ₗ f ∈ M) → (∀ N ≤ M, (∀ k ∈ finU (E := E) (n := n), ∀ f ∈ N, (RU E n k) ∘ₗ f ∈ N) → N = ⊥ ∨ N = M) → IsAutRepU (Submodule.span ℂ {φ | ∃ f ∈ M, ∃ v, f v = φ}) := by
  intro E _ _ _ n S _ _ _ ρ hsp M hM0 hf hk hirr
  let j : M →ₗ[ℂ] S →ₗ[ℂ] (UA E n → ℂ) := M.subtype
  have himg : Submodule.span ℂ {φ | ∃ f ∈ M, ∃ v, f v = φ} = GlobalTheory.DefU.Pairs.img j := by
    unfold GlobalTheory.DefU.Pairs.img
    congr 1
    ext φ
    constructor
    · rintro ⟨f, hf, v, rfl⟩
      exact ⟨⟨f, hf⟩, v, rfl⟩
    · rintro ⟨p, v, rfl⟩
      exact ⟨p.1, p.2, v, rfl⟩
  rw [himg]
  have hj : ∀ (p : M) (x : infU E n) (v : S), j p (ρ x v) = RU E n x.1 (j p v) := fun p x v => (hf p.1 p.2).2 x v
  have hstab : ∀ x, ∀ φ ∈ GlobalTheory.DefU.Pairs.img j, RU E n x φ ∈ GlobalTheory.DefU.Pairs.img j := by
    intro x φ hφ
    refine GlobalTheory.DefU.Pairs.stable_of (fun a => ?_) (fun k => ?_) x φ hφ
    · have h1 : GlobalTheory.DefU.Pairs.img j ≤ (GlobalTheory.DefU.Pairs.img j).comap (RU E n a.1) := Submodule.span_le.2 (by
        rintro _ ⟨p, v, rfl⟩
        change RU E n a.1 _ ∈ GlobalTheory.DefU.Pairs.img j
        rw [← hj]
        exact GlobalTheory.DefU.Pairs.apply_mem_img _ _ _)
      exact fun φ hφ => h1 hφ
    · have h1 : GlobalTheory.DefU.Pairs.img j ≤ (GlobalTheory.DefU.Pairs.img j).comap (RU E n k.1) := Submodule.span_le.2 (by
        rintro _ ⟨p, v, rfl⟩
        exact GlobalTheory.DefU.Pairs.apply_mem_img j ⟨(RU E n k.1) ∘ₗ p.1, hk k k.2 p.1 p.2⟩ v)
      exact fun φ hφ => h1 hφ
  have hne : GlobalTheory.DefU.Pairs.img j ≠ ⊥ := by
    obtain ⟨f, hfM, h0⟩ := (Submodule.ne_bot_iff _).1 hM0
    obtain ⟨v, hv⟩ := DFunLike.ne_iff.1 h0
    intro e
    have := GlobalTheory.DefU.Pairs.apply_mem_img j ⟨f, hfM⟩ v
    rw [e, Submodule.mem_bot] at this
    exact hv this
  let Q : finU (E := E) (n := n) → Module.End ℂ M := fun k =>
    ((LinearMap.llcomp ℂ S (UA E n → ℂ) (UA E n → ℂ) (RU E n k.1)) ∘ₗ M.subtype).codRestrict M
      (fun p => hk k k.2 p.1 p.2)
  have hP : ∀ N : Submodule ℂ M, (∀ k, ∀ p ∈ N, Q k p ∈ N) → N = ⊥ ∨ N = ⊤ := by
    intro N hN
    have hst : ∀ k ∈ finU (E := E) (n := n), ∀ f ∈ N.map M.subtype, (RU E n k) ∘ₗ f ∈ N.map M.subtype := by
      rintro k hkk _ ⟨p, hp, rfl⟩
      exact ⟨Q ⟨k, hkk⟩ p, hN ⟨k, hkk⟩ p hp, rfl⟩
    have hc : N = (N.map M.subtype).comap M.subtype :=
      (Submodule.comap_map_eq_of_injective M.injective_subtype N).symm
    rcases hirr _ (Submodule.map_subtype_le M N) hst with h | h
    · left
      rw [hc, h, Submodule.comap_bot, Submodule.ker_subtype]
    · right
      rw [hc, h, Submodule.comap_subtype_self]
  refine ⟨fun φ hφ => ?_, hstab, hne, fun U hle hU => ?_⟩
  · have h1 : GlobalTheory.DefU.Pairs.img j ≤ autU E n := Submodule.span_le.2 (by
      rintro _ ⟨p, v, rfl⟩
      exact (hf p.1 p.2).1 v)
    exact h1 hφ
  · exact GlobalTheory.DefU.Pairs.eq_bot_or_eq_img hsp (R := fun x => RU E n x.1) hj
      (Q := Q) (T := fun k => RU E n k.1) (fun _ _ _ => rfl) hP hle
      (fun x => hU x.1) (fun k => hU k.1)

end GlobalTheory.FrameAut.VecForms
end
