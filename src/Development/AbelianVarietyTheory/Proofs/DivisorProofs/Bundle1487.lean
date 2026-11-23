module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle456
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle132
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle088
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspidalLieActionOfIsCuspForm
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AdlEqZeroOfMemNbhd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1459
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.HdimEqZeroOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.PreservesFiniteColimitsTwistFunctor
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1430
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1435
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1298
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1446
import GroundTheory.AutomorphicForms.LocallyProfinite
import GroundTheory.AutomorphicForms.Bundle003
import GroundTheory.GlobalFields.KummerTheory.LocalIndex
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical

@[expose] public section

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory

theorem height_diagonal_le_sum (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (r : Fin a → ℝ)
    (d : GL (Fin a) (Cinf E)) (hr : ∀ i, 0 < r i)
    (hd : d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ))) :
    height d ≤ 1 + ∑ i, r i + ∑ i, (r i)⁻¹ := by
  classical
  have hinv : (d⁻¹).val = Matrix.diagonal (fun i => fun _ => (((r i)⁻¹ : ℝ) : ℂ)) := by
    apply Units.inv_eq_of_mul_eq_one_right
    rw [hd, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i w
    have : (r i : ℂ) ≠ 0 := by exact_mod_cast (hr i).ne'
    simp [this]
  have key : ∀ s : Fin a → ℝ, (∀ i, 0 < s i) →
      ‖toL (Matrix.diagonal (fun i => fun (_ : InfinitePlace E) => ((s i : ℝ) : ℂ)))‖ ≤ ∑ i, s i := by
    intro s hs
    have h0 : 0 ≤ ∑ i, s i := Finset.sum_nonneg fun i _ => (hs i).le
    refine (pi_norm_le_iff_of_nonneg h0).2 fun i => (pi_norm_le_iff_of_nonneg h0).2 fun j =>
      (pi_norm_le_iff_of_nonneg h0).2 fun w => ?_
    change ‖(Matrix.diagonal (fun i => fun (_ : InfinitePlace E) => ((s i : ℝ) : ℂ))) i j w‖ ≤ _
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hs i)]
      exact Finset.single_le_sum (fun k _ => (hs k).le) (Finset.mem_univ i)
    · rw [Matrix.diagonal_apply_ne _ hij]
      simpa using h0
  have h1 := key r hr
  have h2 := key (fun i => (r i)⁻¹) (fun i => inv_pos.2 (hr i))
  unfold GlobalTheory.CuspRep.height
  rw [hd, hinv]
  linarith

end GlobalTheory
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory

theorem finite_translates_of_isCompact (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]
    (a : ℕ) (φ : Sm E a) (h : IsOpen {k | finRep E a k φ = φ})
    (Kf : Set (GL (Fin a) (Af E))) (hK : IsCompact Kf) :
    ∃ S : Finset (GL (Fin a) (Af E)), ∀ f ∈ Kf, ∃ f' ∈ S,
      finRep E a f φ = finRep E a f' φ := by
  have hn : ∀ f ∈ Kf, {g | finRep E a g φ = finRep E a f φ} ∈ nhds f := by
    intro f _
    have hc : Continuous (fun g : GL (Fin a) (Af E) => f⁻¹ * g) :=
      continuous_const.mul continuous_id
    have ho := h.preimage hc
    refine Filter.mem_of_superset (ho.mem_nhds ?_) ?_
    · simp
    · intro g hg
      have hg' : finRep E a (f⁻¹ * g) φ = φ := hg
      have e : g = f * (f⁻¹ * g) := by simp
      show finRep E a g φ = finRep E a f φ
      calc finRep E a g φ = finRep E a (f * (f⁻¹ * g)) φ := by rw [← e]
        _ = finRep E a f (finRep E a (f⁻¹ * g) φ) := by rw [map_mul]; rfl
        _ = finRep E a f φ := by rw [hg']
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun f => {g | finRep E a g φ = finRep E a f φ}) hn
  refine ⟨t, fun f hf => ?_⟩
  have := ht hf
  simp only [Set.mem_iUnion] at this
  obtain ⟨f', hf', h'⟩ := this
  exact ⟨f', hf', h'⟩

end GlobalTheory
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Filter

namespace GlobalTheory.JSW.SphVec

open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.LFun

theorem map_mem_twKer {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} {K : Subgroup G}
    (S : V →ₗ[ℂ] W) (hS : ∀ h v, S (ρ h v) = σ h (S v)) {v : V} (hv : v ∈ twKer ρ K 1) : S v ∈ twKer σ K 1 := by
  have h : (twKer ρ K 1).map S ≤ twKer σ K 1 := by
    rw [twKer, Submodule.map_span_le]
    rintro _ ⟨n, u, rfl⟩
    exact Submodule.subset_span ⟨n, S u, by simp [hS]⟩
  exact h ⟨v, hv, rfl⟩

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem exists_fixed_mem (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E))
    (hS : GlobalTheory.LGrp.IsSpherical (π.locRep w) (KGL w (n := a))) (U : Submodule ℂ π.V)
    (hU : ∀ g, ∀ v ∈ U, π.locRep w g v ∈ U) {y : π.V} (hy : y ∈ U) (hy0 : y ≠ 0) :
    ∃ x ∈ U, x ≠ 0 ∧ ∀ k ∈ KGL w (n := a), π.locRep w k x = x := by
  have hK : IsCompact ((KGL w (n := a) : Subgroup _) : Set (GL (Fin a) (w.adicCompletion E))) :=
    (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).2
  have hsm : IsSmooth (π.locRep w) := π.isSmooth_locRep w
  have hsU : IsSmooth (GlobalTheory.PRep.sub (π.locRep w) U hU) := fun v => by
    convert hsm v.1 using 1
    ext g
    exact Subtype.ext_iff
  by_contra hne
  have hbot : fixed (GlobalTheory.PRep.sub (π.locRep w) U hU) (KGL w (n := a)) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    by_contra h0
    exact hne ⟨v.1, v.2, fun h => h0 (Subtype.ext h), fun k hk =>
      congrArg Subtype.val (GlobalTheory.LGrp.mem_fixed.1 hv k hk)⟩
  have htop := (GlobalTheory.LocGL.isCompl_fixed_twKer hsU hK).sup_eq_top
  rw [hbot, bot_sup_eq] at htop
  have hall : ∀ g, π.locRep w g y ∈ twKer (π.locRep w) (KGL w (n := a)) 1 := fun g =>
    map_mem_twKer (ρ := GlobalTheory.PRep.sub (π.locRep w) U hU) U.subtype (fun _ _ => rfl)
      (v := ⟨_, hU g y hy⟩) (htop ▸ Submodule.mem_top)
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hS
  let Wl : Submodule ℂ π.V := ⨅ g, (twKer (π.locRep w) (KGL w (n := a)) 1).comap (π.locRep w g)
  have memWl : ∀ v, v ∈ Wl ↔ ∀ g, π.locRep w g v ∈ twKer (π.locRep w) (KGL w (n := a)) 1 := fun v => by
    simp [Wl, Submodule.mem_iInf]
  have stab : GlobalTheory.CuspRep.IsStable (Wl.map π.V.subtype) := by
    rintro o _ ⟨v, hv, rfl⟩
    obtain ⟨g, S, hS, ho⟩ := GlobalTheory.LocFactor.op_eq_locRep_comp π w o
    have hv' := (memWl v).1 hv
    refine ⟨π.op o v, (memWl _).2 fun h => ?_, rfl⟩
    rw [ho, LinearMap.comp_apply, ← Module.End.mul_apply, ← map_mul]
    have e := LinearMap.congr_fun (hS (h * g)) v
    simp only [LinearMap.comp_apply] at e
    rw [← e]
    exact map_mem_twKer S (fun h v => LinearMap.congr_fun (hS h) v) (hv' (h * g))
  rcases π.irred _ (Submodule.map_subtype_le _ _) stab with h | h
  · have h1 : (y : Sm E a) ∈ Wl.map π.V.subtype := ⟨y, (memWl y).2 hall, rfl⟩
    rw [h, Submodule.mem_bot] at h1
    exact hy0 (Subtype.ext h1)
  · have h1 : (x : Sm E a) ∈ Wl.map π.V.subtype := by rw [h]; exact x.2
    obtain ⟨x', hx', e⟩ := h1
    obtain rfl : x' = x := Subtype.ext e
    have h2 := (memWl x').1 hx' 1
    rw [map_one, Module.End.one_apply] at h2
    exact hx0 (Submodule.disjoint_def.1 (GlobalTheory.LocGL.isCompl_fixed_twKer hsm hK).disjoint x' hx h2)

theorem locRep_comm (π : CuspSub E a) {v w : HeightOneSpectrum (𝓞 E)} (h : w ≠ v)
    (k : GL (Fin a) (v.adicCompletion E)) (g : GL (Fin a) (w.adicCompletion E)) (x : π.V) :
    π.locRep v k (π.locRep w g x) = π.locRep w g (π.locRep v k x) := by
  simp only [CuspSub.locRep, MonoidHom.comp_apply]
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
    LocSph.comm_locGL w _ (pLoc_locGL_of_ne h k)]

theorem exists_fixed_union (π : CuspSub E a) (T : Set (HeightOneSpectrum (𝓞 E))) {y : π.V} (hy0 : y ≠ 0)
    (hy : ∀ v ∈ T, ∀ k ∈ KGL v (n := a), π.locRep v k y = y) (F : Finset (HeightOneSpectrum (𝓞 E)))
    (hF : ∀ w ∈ F, GlobalTheory.LGrp.IsSpherical (π.locRep w) (KGL w (n := a))) :
    ∃ x : π.V, x ≠ 0 ∧ ∀ v, v ∈ T ∨ v ∈ F → ∀ k ∈ KGL v (n := a), π.locRep v k x = x := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨y, hy0, fun v hv => hy v (by simpa using hv)⟩
  | insert w F _ ih =>
    obtain ⟨x, hx0, hx⟩ := ih fun v hv => hF v (Finset.mem_insert_of_mem hv)
    let U : Submodule ℂ π.V := ⨅ v : {v // (v ∈ T ∨ v ∈ F) ∧ w ≠ v}, fixed (π.locRep v.1) (KGL v.1 (n := a))
    have memU : ∀ z, z ∈ U ↔ ∀ v, (v ∈ T ∨ v ∈ F) → w ≠ v → ∀ k ∈ KGL v (n := a), π.locRep v k z = z := fun z => by
      simp only [U, Submodule.mem_iInf, GlobalTheory.LGrp.mem_fixed, Subtype.forall]
      exact ⟨fun h v h1 h2 => h v ⟨h1, h2⟩, fun h v h1 => h v h1.1 h1.2⟩
    obtain ⟨z, hz, hz0, hzw⟩ := exists_fixed_mem π w (hF w (Finset.mem_insert_self _ _)) U
      (fun g z hz => (memU _).2 fun v hv hne k hk => by
        rw [locRep_comm π hne, (memU z).1 hz v hv hne k hk])
      ((memU x).2 fun v hv _ => hx v hv) hx0
    refine ⟨z, hz0, fun v hv => ?_⟩
    by_cases hne : w = v
    · subst hne; exact hzw
    · refine (memU z).1 hz v (hv.imp_right fun h => ?_) hne
      exact (Finset.mem_insert.1 h).resolve_left fun e => hne e.symm

theorem exists_sphVec_of_isSpherical (π : CuspSub E a) (S : Set (HeightOneSpectrum (𝓞 E)))
    (hS : ∀ w ∉ S, GlobalTheory.LGrp.IsSpherical (π.locRep w) (KGL w (n := a))) :
    ∃ φ ∈ π.V, φ ≠ 0 ∧ ∀ w ∉ S, ∀ k ∈ KGL w (n := a), act (.fin (locGL E a w k)) φ = φ := by
  classical
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  have hev := LocSph.eventually_mem ((π.cusp φ hφ).1.level.mem_nhds (by simp))
  rw [Filter.eventually_cofinite] at hev
  obtain ⟨x, hx0, hx⟩ := exists_fixed_union π
    {w | ∀ g : GL (Fin a) (w.adicCompletionIntegers E),
      locGL E a w (GeneralLinearGroup.map (w.adicCompletionIntegers E).subtype g) ∈ {k | finRep E a k φ = φ}}
    (y := ⟨φ, hφ⟩) (fun h => h0 (congrArg Subtype.val h))
    (by rintro v hv _ ⟨g, rfl⟩; exact Subtype.ext (hv g))
    (hev.toFinset.filter (· ∉ S)) (fun w hw => hS w (Finset.mem_filter.1 hw).2)
  refine ⟨x.1, x.2, fun h => hx0 (Subtype.ext h), fun w hw k hk => congrArg Subtype.val (hx w ?_ k hk)⟩
  refine (em _).imp_right fun h => Finset.mem_filter.2 ⟨hev.mem_toFinset.2 h, hw⟩

theorem exists_sphVec (π : CuspSub E a) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hS : ∀ w ∉ S, ∃ B, HasSatGL w (π.locRep w) B) :
    ∃ φ ∈ π.V, φ ≠ 0 ∧ ∀ w ∉ S, ∀ k ∈ KGL w (n := a), act (.fin (locGL E a w k)) φ = φ :=
  exists_sphVec_of_isSpherical π S fun w hw => (hS w hw).elim fun _ h => h.1

theorem exists_sphVec_of_hasSat (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (B : HeightOneSpectrum (𝓞 E) → Multiset ℂˣ)
    (h : ∀ w ∉ S, HasSatGL w (π.locRep w) (B w)) :
    ∃ φ ∈ π.V, φ ≠ 0 ∧ ∀ w ∉ S, ∀ k ∈ KGL w (n := a), act (.fin (locGL E a w k)) φ = φ :=
  exists_sphVec π S fun w hw => ⟨B w, h w hw⟩

end GlobalTheory.JSW.SphVec
end
end

section

open NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LFun.SphComp

theorem hasSatake_of_isLocComp : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {m : ℕ} (π : GlobalTheory.CuspRep.CuspSub E m) {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ}, GlobalTheory.LFun.HasSatGL w (π.locRep w) B → ∀ {σ : GlobalTheory.CuspRep.SmIrr (GL (Fin m) (w.adicCompletion E))}, π.IsLocComp w σ → ∃ α : Fin m → ℂˣ, Finset.univ.val.map α = B ∧ GlobalTheory.SmGL.HasSatake σ.ρ α := by
  intro E _ _ _ m π w B hB σ hσ
  obtain ⟨f, hf0, hf⟩ := hσ
  obtain ⟨x, hx⟩ := hB.exists_vec

  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]
    refine (((GlobalTheory.CuspRep.isIrreducible_iff σ.ρ).1 σ.irred).2 _ fun g u hu => ?_).resolve_right fun h => hf0 ?_
    · rw [LinearMap.mem_ker] at hu ⊢; rw [hf, hu, map_zero]
    · exact LinearMap.ext fun u => by
        have : u ∈ LinearMap.ker f := h ▸ Submodule.mem_top
        simpa using this

  obtain ⟨v, hv0, hvK⟩ : ∃ v : σ.V, v ≠ 0 ∧ ∀ k ∈ (GlobalTheory.LFun.KGL w (n := m) : Set _), σ.ρ k v = v := by
    refine GlobalTheory.CuspRep.LocSph.exists_fixed_of_mem_iSup ((GlobalTheory.CuspRep.finRep E m).comp (GlobalTheory.CuspRep.locGL E m w)) σ.ρ
      σ.irred (fun i : GlobalTheory.CuspRep.LocSph.Maps π w σ => i.1) (fun i g u => i.2.2 g u) _ (x : GlobalTheory.CuspRep.Sm E m)
      (fun h => hx.1 (Subtype.ext h)) (fun k hk => ?_) ?_
    · exact congrArg Subtype.val (GlobalTheory.LGrp.mem_fixed.1 hx.2.1 k hk)
    · rw [GlobalTheory.CuspRep.LocSph.iSup_range_eq π w σ ⟨f, hf0, hf⟩]; exact x.2
  have hfv : f v ≠ 0 := fun h => hv0 (hinj (h.trans (map_zero f).symm))
  have hs : GlobalTheory.LFun.IsSatVecGL w σ.ρ v B := GlobalTheory.LFun.IsSatVecGL.of_map f hf hinj
    (hB.2 _ (GlobalTheory.LGrp.mem_fixed.2 fun k hk => by rw [← hf, hvK k hk]) hfv)
  exact (GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff _ (Fin m) σ.V σ.ρ B).1
    (GlobalTheory.LFun.SatCompare.hasSatakeGL_of_isSatVecGL ⟨σ.smooth, σ.irred⟩ hs)

end GlobalTheory.LFun.SphComp
end

section

noncomputable section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open Topology

namespace GlobalTheory.CuspRep

theorem discreteTopology_ratN (E : Type) [Field E] [NumberField E] (a s : ℕ) :
    DiscreteTopology (ratN E a s) := by
  refine discreteTopology_of_isOpen_singleton_zero ?_
  have hU : IsOpen (Set.univ.pi fun _ : BlockIx a s => Formalism.IndefR.Eqv.G5.adlNbhd (F := E)) :=
    isOpen_set_pi Set.finite_univ fun _ _ => Formalism.IndefR.Eqv.G5.adl_isOpen_nbhd
  have h : ({0} : Set (ratN E a s)) =
      Subtype.val ⁻¹' (Set.univ.pi fun _ : BlockIx a s => Formalism.IndefR.Eqv.G5.adlNbhd (F := E)) := by
    ext ⟨x, q, hq⟩
    constructor
    · intro hx p _
      have : x = 0 := congrArg Subtype.val hx
      subst this
      exact Formalism.IndefR.Eqv.G5.adl_zero_mem_nbhd
    · intro hx
      subst hq
      apply Subtype.ext
      funext p
      have h0 : q p = 0 := Formalism.IndefR.Eqv.G5.adl_eq_zero_of_mem_nbhd (q p) (hx p (Set.mem_univ _))
      show algebraMap E (Ad E) (q p) = 0
      rw [h0, map_zero]
  rw [h]
  exact hU.preimage continuous_subtype_val

theorem exists_isAddFundamentalDomain_ratN : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (s : ℕ) [MeasurableSpace (BlockIx a s → Ad E)] [BorelSpace (BlockIx a s → Ad E)] (μ : Measure (BlockIx a s → Ad E)) [μ.IsAddHaarMeasure], ∃ 𝓕 : Set (BlockIx a s → Ad E), IsAddFundamentalDomain (ratN E a s) 𝓕 μ ∧ μ 𝓕 ≠ 0 ∧ μ 𝓕 < ⊤ := by
  intro E _ _ _ a s _ _ μ _
  haveI : SecondCountableTopology (Ad E) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  haveI := discreteTopology_ratN E a s
  haveI := countable_ratN (E := E) (a := a) s
  obtain ⟨D, -, -, hD⟩ := GlobalTheory.exists_isAddFundamentalDomain_addSubgroup (ratN E a s)
  haveI : MeasurableConstVAdd (ratN E a s) (BlockIx a s → Ad E) :=
    ⟨fun γ => (continuous_const.add continuous_id :
      Continuous fun x : BlockIx a s → Ad E => (γ : BlockIx a s → Ad E) + x).measurable⟩
  haveI : VAddInvariantMeasure (ratN E a s) (BlockIx a s → Ad E) μ :=
    ⟨fun γ t _ => measure_preimage_add μ (γ : BlockIx a s → Ad E) t⟩
  have hμ : μ ≠ 0 := fun h => by
    have := isOpen_univ.measure_ne_zero μ Set.univ_nonempty
    rw [h] at this
    exact this rfl
  exact ⟨D, hD μ, (hD μ).measure_ne_zero hμ, covol_lt_top μ D (hD μ)⟩

end GlobalTheory.CuspRep
end
end

section

open NumberField MeasureTheory GlobalTheory.CuspRep

theorem _root_.GlobalTheory.T.constant_term_center_action_smooth_form : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ) [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 → ∀ φ : Sm E a, (∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g) → IsOpen {k | finRep E a k φ = φ} → ∀ z ∈ Zalg E a, ∀ c : Sm E a, c.1 = (fun g : GA E a => ∫ x in 𝓕, φ.1 (unip x * g) ∂μ) → (z c).1 = fun g : GA E a => ∫ x in 𝓕, (z φ).1 (unip x * g) ∂μ := by
  first | exact @GlobalTheory.ConstTermZalg.constTerm_zalg | exact GlobalTheory.ConstTermZalg.constTerm_zalg | (intros; apply GlobalTheory.ConstTermZalg.constTerm_zalg <;> assumption)
end

section

namespace GlobalTheory.ContinuousRepresentationCoefficients

theorem continuous_coeff_of_separating {X V ι : Type} [TopologicalSpace X] [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (L : ι → V →ₗ[ℂ] ℂ)
    (hL : ∀ v, (∀ i, L i v = 0) → v = 0) (f : X → V) (hf : ∀ i, Continuous fun x => L i (f x))
    (ℓ : Module.Dual ℂ V) : Continuous fun x => ℓ (f x) := by
  have hmem : ℓ ∈ Submodule.span ℂ (Set.range L) := by
    apply FiniteDimensional.mem_span_of_iInf_ker_le_ker
    intro v hv
    have h0 : v = 0 := hL v fun i => by
      simpa using (Submodule.mem_iInf _).1 hv i
    simp [h0]
  induction hmem using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hf i
  | zero => simpa using continuous_const
  | add x y _ _ hx hy => exact hx.add hy
  | smul c x _ hx => exact (continuous_const (y := c)).mul hx

theorem continuous_translate {E : Type} [Field E] [NumberField E] [NumberField.IsTotallyComplex E]
    {a : ℕ} (φ : GlobalTheory.CuspRep.Sm E a) (g : GlobalTheory.CuspRep.GA E a) :
    Continuous fun k : GlobalTheory.CuspRep.Kinf E a =>
      ((GlobalTheory.CuspRep.cptRep E a k φ : GlobalTheory.CuspRep.Sm E a) : GlobalTheory.CuspRep.GA E a → ℂ) g := by
  have h1 : ContinuousOn (GlobalTheory.CuspRep.chart φ.1 g) (GlobalTheory.CuspRep.invSet E a) :=
    (φ.2 g).continuousOn
  have hu : ∀ k : GlobalTheory.CuspRep.Kinf E a,
      IsUnit (Matrix.of (k.1 : GlobalTheory.CuspRep.Lie E a)) := fun k => (Unitary.toUnits k).isUnit
  have h2 : Continuous fun k : GlobalTheory.CuspRep.Kinf E a => (k.1 : GlobalTheory.CuspRep.Lie E a) :=
    continuous_subtype_val
  have h3 := h1.comp_continuous h2 hu
  refine h3.congr fun k => ?_
  have h4 : (hu k).unit = Unitary.toUnits k := Units.ext rfl
  show GlobalTheory.CuspRep.chart φ.1 g (k.1 : GlobalTheory.CuspRep.Lie E a) = _
  unfold GlobalTheory.CuspRep.chart
  rw [dite_eq_left (hu k), h4]
  rfl

theorem isContRep_sub {E : Type} [Field E] [NumberField E] [NumberField.IsTotallyComplex E]
    {a : ℕ} (W : Submodule ℂ (GlobalTheory.CuspRep.Sm E a))
    (hW : ∀ (k : GlobalTheory.CuspRep.Kinf E a), ∀ w ∈ W, GlobalTheory.CuspRep.cptRep E a k w ∈ W)
    [FiniteDimensional ℂ W] :
    GlobalTheory.Published.AutFin.IsContRep (GlobalTheory.PRep.sub (GlobalTheory.CuspRep.cptRep E a) W hW) := by
  intro ℓ w
  refine continuous_coeff_of_separating
    (fun g : GlobalTheory.CuspRep.GA E a =>
      (LinearMap.proj g : (GlobalTheory.CuspRep.GA E a → ℂ) →ₗ[ℂ] ℂ) ∘ₗ
        (GlobalTheory.CuspRep.Sm E a).subtype ∘ₗ W.subtype) ?_ _ ?_ ℓ
  · intro v hv
    exact Subtype.ext (Subtype.ext (funext hv))
  · intro g
    exact continuous_translate w.1 g

end GlobalTheory.ContinuousRepresentationCoefficients
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory

theorem genericPoint_mem_of_mem_opens (Y : Scheme.{0}) [IsIntegral Y] (W : Y.Opens) {y : Y}
    (hy : y ∈ W) : genericPoint Y ∈ W :=
  ((genericPoint_spec Y).mem_open_set_iff W.isOpen).mpr ⟨y, trivial, hy⟩

theorem ratsec_split_of_H1 : ∀ (Y : Scheme.{0}) [IsIntegral Y] (D : CartierDiv Y) (W₁ W₂ : Y.Opens),
    Subsingleton (cohOn (twist (GlobalTheory.structureModule Y) (toLB D)) (W₁ ⊔ W₂) 1) →
    ∀ f : Y.functionField, (∀ y ∈ W₁ ⊓ W₂, D.RegularAt y f) →
    ∃ h₁ h₂ : Y.functionField, f = h₂ - h₁ ∧ (∀ y ∈ W₁, D.RegularAt y h₁) ∧
      ∀ y ∈ W₂, D.RegularAt y h₂ := by
  intro Y _ D W₁ W₂ hH f hf
  obtain ⟨ρ, hreg, hsurj, hres⟩ := GlobalTheory.T.exists_rationalFunction_maps_of_cartierTwistSections Y D
  by_cases g1 : genericPoint Y ∈ W₁
  · by_cases g2 : genericPoint Y ∈ W₂
    · have g12 : genericPoint Y ∈ W₁ ⊓ W₂ := ⟨g1, g2⟩
      obtain ⟨t, ht⟩ := hsurj (W₁ ⊓ W₂) f g12 hf
      obtain ⟨a, b, hab⟩ := GlobalTheory.T.mayer_vietoris_sections_split Y _ W₁ W₂ hH t
      refine ⟨ρ W₁ a, ρ W₂ b, ?_, fun y hy => hreg W₁ a y hy, fun y hy => hreg W₂ b y hy⟩
      rw [← ht, hab, map_sub, hres W₂ (W₁ ⊓ W₂) inf_le_right b g12,
        hres W₁ (W₁ ⊓ W₂) inf_le_left a g12]
    · refine ⟨ρ W₁ 0, f, by simp, fun y hy => hreg W₁ 0 y hy, fun y hy => ?_⟩
      exact absurd (genericPoint_mem_of_mem_opens Y W₂ hy) g2
  · refine ⟨-f, ρ W₂ 0, by simp, fun y hy => ?_, fun y hy => hreg W₂ 0 y hy⟩
    exact absurd (genericPoint_mem_of_mem_opens Y W₁ hy) g1

end GlobalTheory
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
namespace GlobalTheory.IdGenRat

theorem presents_lbPow_toLB {X : Scheme.{0}} [IsIntegral X] (A : CartierDiv X) (l : ℕ) :
    ∃ r, Presents (l • A) (lbPow (toLB A) l) r := by
  have h := GlobalTheory.CombChern.presents_zpow (presents_toLB A) (l : ℤ)
  rw [natCast_zsmul] at h
  exact ⟨_, h⟩

theorem exists_sections_vanish_generate : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (A : CartierDiv X) (z : X), IsAmpleLB (toLB A) → ∃ l₁ : ℕ, ∀ l, l₁ ≤ l → ∃ (r : ℕ) (κ : Fin r → X.functionField), (∀ i, κ i ∈ (l • A).sections) ∧ (∀ i, (l • A).VanishesAt z (κ i)) ∧ ∀ y, ¬ z ⤳ y → ∃ i, (l • A).GeneratesAt y (κ i) := by
  intro X _ _ p hp A z hA
  obtain ⟨l₁, hl₁⟩ := Filter.eventually_atTop.1
    (GlobalTheory.T.eventually_exists_ample_pow_sections_cutting_out_closed X p hp (toLB A) (Closeds.closure {z}) hA)
  refine ⟨l₁, fun l hl => ?_⟩
  obtain ⟨r, κ, -, hz, hy⟩ := hl₁ l hl
  obtain ⟨ρ, hρ⟩ := presents_lbPow_toLB A l
  refine ⟨r, fun i => hρ.rat (κ i), fun i => hρ.rat_mem _, fun i => ?_, fun y hy' => ?_⟩
  · exact (hρ.vanishesAt_rat_iff _).2 (hz i z (subset_closure rfl))
  · have hyZ : y ∉ Closeds.closure ({z} : Set X) := fun h => hy' (specializes_iff_mem_closure.2 h)
    obtain ⟨i, hi⟩ := hy y hyZ
    exact ⟨i, (hρ.generatesAt_rat_iff _).2 hi⟩

end GlobalTheory.IdGenRat
end
