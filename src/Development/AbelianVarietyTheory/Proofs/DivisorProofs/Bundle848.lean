module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle456
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
public import Mathlib.RingTheory.HopfAlgebra.Quotient
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle830
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle411
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle578
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle837
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle819
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FibreFramesOnModels
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle027
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.LevelCuspCharacters
public import Mathlib.Algebra.Polynomial.Mirror
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle820
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle821
public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle822
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Finiteness.Lattice
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.PhiPowSt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDiv

theorem isHopfIdeal_kerIdeal {R A C : Type} [CommRing R] [CommRing A] [CommRing C]
    [HopfAlgebra R A] [HopfAlgebra R C] (f : C →ₐc[R] A) : (kerIdeal f).IsHopfIdeal R := by
  apply GlobalTheory.PDiv.isHopfIdeal_kerIdeal_of_bialgHom <;> assumption

theorem isCocomm_of_surjective {R A B : Type} [CommRing R] [CommRing A] [CommRing B]
    [Bialgebra R A] [Bialgebra R B] [IsCocomm R A] (f : A →ₐc[R] B)
    (hf : Function.Surjective f) : IsCocomm R B := by
    refine ⟨LinearMap.ext fun b => ?_⟩
    obtain ⟨a, rfl⟩ := hf b
    have h1 := CoalgHomClass.map_comp_comul_apply f a
    have h2 := TensorProduct.map_comm (f : A →ₗ[R] B) (f : A →ₗ[R] B) (comul (R := R) a)
    have h3 := Coalgebra.comm_comul R a
    show TensorProduct.comm R B B (comul (f a)) = comul (f a)
    rw [← h1, ← h2, h3]

end GlobalTheory.PDiv

namespace GlobalTheory.PDivGroup

theorem exists_cobOne_relFrob_eq_zero_dUnit_eq (p : ℕ) [Fact p.Prime] (K : Type) [Field K]
    (h : (p : K) = 0) (G : PDivGroup p K) (w : Cot K ((frobTwist h G).A 1)) :
    ∃ (β : (frobTwist h G).A 1) (w' : Cot K (G.A 1)),
      cobOne K (G.A 1) ((relFrob h G).app 1 β) = 0 ∧
        dUnit (R := K) β = w + cotMap ((verschiebung h G).app 1) w' := by
    have : CharP K p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr h
    let V := (verschiebung h G).app 1
    let F := (relFrob h G).app 1
    let J : Ideal ((frobTwist h G).A 1) := kerIdeal V
    have : J.IsHopfIdeal K := GlobalTheory.PDiv.isHopfIdeal_kerIdeal V
    let π : (frobTwist h G).A 1 →ₐc[K] (frobTwist h G).A 1 ⧸ J := Bialgebra.Quotient.mkBialgHom J
    have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
    have hπker : RingHom.ker π = J := Ideal.Quotient.mkₐ_ker K J
    have : IsCocomm K ((frobTwist h G).A 1 ⧸ J) := GlobalTheory.PDiv.isCocomm_of_surjective π hπ
    have : Module.Finite K ((frobTwist h G).A 1 ⧸ J) :=
      Module.Finite.of_surjective (π : (frobTwist h G).A 1 →ₗ[K] _) hπ

    have hπV : ∀ a : G.A 1, π (V a) = algebraMap K _ (counit (R := K) a) :=
      (kerIdeal_le_ker_iff V (AlgHom.ofClass π)).mp hπker.ge

    have hdual : ∀ φ ∈ augIdeal K (CartierDual K ((frobTwist h G).A 1 ⧸ J)), φ ^ p = 0 := by
      intro φ hφ
      have hφ1 : φ 1 = 0 := by
        have : counit (R := K) φ = 0 := by simpa using hφ
        simpa using this
      have hχ : (CartierDual.map π φ) ^ p = 0 := by
        apply pow_char_eq_zero_of_verschiebung p K h G 1
        intro a
        rw [CartierDual.map_apply, hπV, Algebra.algebraMap_eq_smul_one]
        change φ.ofConv (counit (R := K) a • 1) = 0
        rw [map_smul]
        change counit (R := K) a • φ 1 = 0
        rw [hφ1, smul_zero]
      have hχ' : CartierDual.map π (φ ^ p) = 0 := by rw [map_pow]; exact hχ
      apply CartierDual.ext_apply
      intro x
      obtain ⟨a, rfl⟩ := hπ x
      have := congrArg (fun χ : CartierDual K ((frobTwist h G).A 1) => χ a) hχ'
      simp only [CartierDual.map_apply] at this
      simpa using this
    obtain ⟨b, hb0, hbw⟩ :=
      exists_primitive_dUnit_eq p K ((frobTwist h G).A 1 ⧸ J) hdual (cotMap π w)
    obtain ⟨β, rfl⟩ := hπ b

    have hker : RingHom.ker π ≤ RingHom.ker F := by
      rw [hπker]
      exact app_one_eq_zero_of_mem_kerIdeal_of_comp_eq_prime_smul p K (frobTwist h G) G
        (verschiebung h G) (relFrob h G) (relFrob_comp_verschiebung h G)
    have hFβ : F β = liftSurj π hπ F hker (π β) := (liftSurj_apply π hπ F hker β).symm

    obtain ⟨w', hw'⟩ := (exact_cotMap hπ V hπker (dUnit (R := K) β - w)).mp (by
      rw [map_sub, cotMap_d, hbw, sub_self])
    refine ⟨β, w', ?_, ?_⟩
    · rw [hFβ, ← pullTwo_cobOne, hb0, map_zero]
    · rw [hw']
      abel

end GlobalTheory.PDivGroup
end
end

section

open NumberField

theorem _root_.GlobalTheory.T.completed_heckePartialLSeries_entire_bounded_strips : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ (n : I → ℤ), (∃ i, n i ≠ 0) → ∀ (M : Ideal (𝓞 K)) (F : 𝓞 K → ℂ), M ≠ ⊥ → (∀ α μ : 𝓞 K, μ ∈ M → F (α + μ) = F α) → (∀ (u : (𝓞 K)ˣ) (α : 𝓞 K), F ((u : 𝓞 K) * α) * GlobalTheory.HeckeStrip.wt φ n (((u : 𝓞 K) * α : 𝓞 K) : K) = F α * GlobalTheory.HeckeStrip.wt φ n (α : K)) → ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧ GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.BoundedInStrips Λ ∧ ∀ s : ℂ, 1 < s.re → Λ s = GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.archFactor n s * GlobalTheory.HeckeStrip.pSeries F φ n s := by
  first | exact @GlobalTheory.HeckeStrip.completed_pSeries_entire_bounded | exact GlobalTheory.HeckeStrip.completed_pSeries_entire_bounded | (intros; apply GlobalTheory.HeckeStrip.completed_pSeries_entire_bounded <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.KeySwapSec

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open ReciprocityTheory.ChartRestriction.G.H1

theorem exists_isFibreOf_of_isMul (R R' : Type) [CommRing R] [CommRing R'] (f : R →+* R') (G : Over (Sp R)) [GrpObj G]
    [IsCommMonObj G] (L : LB G.left) (rig : LB.Gen (L.pull (eSec G))) (θ : L.Sec) (n : ℕ) (w : Fin n → (epsR R ⟶ G))
    (x : KeyIn R') (hL : L.IsLB) (hx : IsFibreOf x G L rig θ w f) (θ₀ : L.Sec) (b : R) (hb : IsMul (X := G) θ b θ₀) :
    ∃ (th₀ : x.P.L.Sec) (hth₀ : ∀ s : Sp R', ∃ z : x.P.A.left, x.P.A.hom z = s ∧ z ∈ Out.nonzeroLocus th₀),
      (∀ i, LB.Sec.f x.th i = constFn x.P.A.hom _ (f b) * LB.Sec.f th₀ i) ∧
      IsFibreOf ⟨x.P, x.g_pos, x.rig, x.rig_gen, th₀, hth₀, x.v, x.basis⟩ G L rig θ₀ w f := by
  obtain ⟨φ, he, e, hg, F, hp, hgen, hr, hs, hF, hFe, hv⟩ := hx
  obtain ⟨th₀, h₀⟩ := sec_pull_down ((isGen_iff e).1 hgen) hL x.P.isLB θ₀
  have h₁ := (KeyCancel.appLE_eq_iff_stalk e θ x.th).1 hs
  have hm : ∀ i, LB.Sec.f x.th i = constFn x.P.A.hom _ (f b) * LB.Sec.f th₀ i := by
    refine (sec_eq_iff _ _ _ _).2 fun k y hk => ?_
    obtain ⟨j, hj⟩ := exists_chart hL (φ y)
    have e₁ := h₁ _ (𝟙 _) y j k hj hk
    have e₀ := h₀ _ (𝟙 _) y j k hj hk
    rw [hb j, gs_mul (𝟙 _ ≫ φ) y _ hj, gs_constFn _ _ (𝟙 _ ≫ φ) y hj, e₀, Category.id_comp, hp.1.w, cst_comp,
      mul_left_comm] at e₁
    exact ((Units.mul_right_inj _).1 e₁).symm
  refine ⟨th₀, fun s => ?_, hm, φ, he, e, hg, F, hp, hgen, hr, (KeyCancel.appLE_eq_iff_stalk e θ₀ th₀).2 h₀, hF, hFe, hv⟩
  obtain ⟨z, hz, hne⟩ := x.th_ne s
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hne
  refine ⟨z, hz, TopologicalSpace.Opens.mem_iSup.2 ⟨k, ?_⟩⟩
  rw [hm k, Scheme.basicOpen_mul] at hk
  exact hk.2

end GlobalTheory.KeySwapSec
end
end

section

open Polynomial

noncomputable section

namespace GlobalTheory.CuspInv

open GlobalTheory.IndefiniteRowSideFullHecke

def mirrorEquiv (k : Type) [Field k] : k[X] ≃* k[X] where
  toFun := mirror
  invFun := mirror
  left_inv := fun f => mirror_mirror f
  right_inv := fun f => mirror_mirror f
  map_mul' := fun f g => mirror_mul_of_domain f g

theorem powIrr_of_inv {k ι : Type} [Field k] [Fintype ι] [DecidableEq ι] (h h' : Matrix ι ι k)
    (hh : h * h' = 1) (H : ∃ (φ : k[X]) (n : ℕ), Irreducible φ ∧ h.charpoly = φ ^ n) :
    ∃ (φ : k[X]) (n : ℕ), Irreducible φ ∧ h'.charpoly = φ ^ n := by
  classical
  obtain ⟨φ, n, hφ, hn⟩ := H
  have hu : IsUnit h := (Matrix.isUnit_iff_isUnit_det h).2 (Matrix.isUnit_det_of_right_inverse hh)
  have hinv : h' = h⁻¹ := (Matrix.inv_eq_right_inv hh).symm
  have hdet : h.det ≠ 0 := (Matrix.isUnit_det_of_right_inverse hh).ne_zero
  have h0 : h.charpoly.coeff 0 ≠ 0 := by
    intro h0
    exact hdet (by rw [Matrix.det_eq_sign_charpoly_coeff, h0, mul_zero])
  have hm : h.charpoly.mirror = h.charpolyRev := by
    rw [mirror, natTrailingDegree_eq_zero_of_constantCoeff_ne_zero (p := h.charpoly) h0, pow_zero, mul_one,
      Matrix.reverse_charpoly]
  have hψ : Irreducible (mirrorEquiv k φ) := (MulEquiv.irreducible_iff (mirrorEquiv k)).2 hφ
  have h1 : h.charpolyRev = (mirrorEquiv k φ) ^ n := by
    rw [← map_pow, ← hn, ← hm]; rfl
  have hass : Associated h'.charpoly ((normalize (mirrorEquiv k φ)) ^ n) := by
    refine Associated.trans ?_ ((associated_normalize _).pow_pow)
    rw [hinv, Matrix.charpoly_inv h hu, h1]
    refine associated_unit_mul_left _ _ ?_
    refine IsUnit.mul (IsUnit.pow _ isUnit_one.neg) ?_
    rw [isUnit_C, Ring.inverse_eq_inv', isUnit_iff_ne_zero]
    exact inv_ne_zero hdet
  refine ⟨normalize (mirrorEquiv k φ), n, (associated_normalize _).irreducible hψ, ?_⟩
  exact eq_of_monic_of_associated h'.charpoly_monic ((monic_normalize hψ.ne_zero).pow n) hass

theorem eigenspace_le {L V : Type} [Field L] [AddCommGroup V] [Module L V] (f g : Module.End L V)
    (hfg : g * f = 1) (z : L) : f.eigenspace z ≤ g.eigenspace z⁻¹ := by
  intro v hv
  rw [Module.End.mem_eigenspace_iff] at hv ⊢
  have h1 : g (f v) = v := by rw [← Module.End.mul_apply, hfg]; rfl
  rw [hv, map_smul] at h1
  by_cases hz : z = 0
  · subst hz
    rw [zero_smul] at h1
    rw [← h1]; simp
  · conv_rhs => rw [← h1]
    rw [smul_smul, inv_mul_cancel₀ hz, one_smul]

theorem eigenspace_inv {L V : Type} [Field L] [AddCommGroup V] [Module L V] (f g : Module.End L V)
    (hfg : f * g = 1) (hgf : g * f = 1) (z : L) : g.eigenspace z⁻¹ = f.eigenspace z := by
  refine le_antisymm ?_ (eigenspace_le f g hgf z)
  simpa using eigenspace_le g f hfg z⁻¹

theorem mem_aroots_iff {k L ι : Type} [Field k] [Field L] [Algebra k L] [Fintype ι] [DecidableEq ι]
    (h : Matrix ι ι k) (z : L) :
    z ∈ h.charpoly.aroots L ↔
      Module.End.eigenspace (Matrix.toLin' (h.map (algebraMap k L))) z ≠ ⊥ := by
  rw [← Module.End.hasEigenvalue_iff, Module.End.hasEigenvalue_iff_isRoot_charpoly,
    Matrix.charpoly_toLin', Matrix.charpoly_map, mem_aroots, IsRoot, eval_map_algebraMap]
  simp [h.charpoly_monic.ne_zero]

theorem torVal_inv {p : ℕ} [Fact p.Prime] {K : Type} [Field K] {d : ℕ} (θ : LevelCuspCharacters.Tor p d →* Kˣ)
    (z : LevelCuspCharacters.Fbar p) : LevelCuspCharacters.torVal θ⁻¹ z = LevelCuspCharacters.torVal θ z⁻¹ := by
  have hinj : Function.Injective
      (fun u : LevelCuspCharacters.Tor p d => ((u : (LevelCuspCharacters.Fbar p)ˣ) : LevelCuspCharacters.Fbar p)) :=
    fun a b hab => Subtype.ext (Units.ext hab)
  unfold LevelCuspCharacters.torVal
  by_cases hz : ∃ u : LevelCuspCharacters.Tor p d, ((u : (LevelCuspCharacters.Fbar p)ˣ) : LevelCuspCharacters.Fbar p) = z
  · obtain ⟨u, rfl⟩ := hz
    have h2 : (((u : (LevelCuspCharacters.Fbar p)ˣ) : LevelCuspCharacters.Fbar p))⁻¹ =
        (((u⁻¹ : LevelCuspCharacters.Tor p d) : (LevelCuspCharacters.Fbar p)ˣ) : LevelCuspCharacters.Fbar p) := by simp
    rw [h2, hinj.extend_apply, hinj.extend_apply]
    simp
  · rw [Function.extend_apply' _ _ _ hz, Function.extend_apply']
    · rfl
    · rintro ⟨u, hu⟩
      exact hz ⟨u⁻¹, by simp [hu]⟩

theorem cuspChar_inv : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (ι : Type) [Fintype ι]
    [DecidableEq ι] (θ : LevelCuspCharacters.Tor p (Fintype.card ι) →* Kˣ) (h h' : Matrix ι ι (ZMod p)),
    h * h' = 1 → LevelCuspCharacters.cuspChar θ⁻¹ h = LevelCuspCharacters.cuspChar θ h' := by
  intro p _ K _ ι _ _ θ h h' hh
  classical
  have hh' : h' * h = 1 := mul_eq_one_comm.1 hh
  have key : ∀ (a b : Matrix ι ι (ZMod p)), a * b = 1 →
      Matrix.toLin' (a.map (algebraMap (ZMod p) (LevelCuspCharacters.Fbar p))) *
        Matrix.toLin' (b.map (algebraMap (ZMod p) (LevelCuspCharacters.Fbar p))) = 1 := by
    intro a b hab
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.map_mul, hab,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.toLin'_one]
    rfl
  have heig := eigenspace_inv _ _ (key h h' hh) (key h' h hh')
  have hmem : ∀ z : LevelCuspCharacters.Fbar p, z ∈ (h.charpoly.aroots (LevelCuspCharacters.Fbar p)).toFinset ↔
      z⁻¹ ∈ (h'.charpoly.aroots (LevelCuspCharacters.Fbar p)).toFinset := by
    intro z
    rw [Multiset.mem_toFinset, Multiset.mem_toFinset, mem_aroots_iff, mem_aroots_iff, heig]
  have hcard : (h.charpoly.aroots (LevelCuspCharacters.Fbar p)).toFinset.card =
      (h'.charpoly.aroots (LevelCuspCharacters.Fbar p)).toFinset.card :=
    Finset.card_bijective _ inv_involutive.bijective hmem
  unfold LevelCuspCharacters.cuspChar
  by_cases H : ∃ (φ : (ZMod p)[X]) (n : ℕ), Irreducible φ ∧ h.charpoly = φ ^ n
  · rw [if_pos H, if_pos (powIrr_of_inv h h' hh H)]
    congr 1
    refine Finset.sum_bijective _ inv_involutive.bijective (by convert hmem) ?_
    intro z _
    rw [torVal_inv, heig]
    congr 2
    funext i
    congr 3
  · rw [if_neg H, if_neg (fun H' => H (powIrr_of_inv h' h hh' H'))]

end GlobalTheory.CuspInv
end
end

section

open NumberField GlobalTheory.CuspRep

theorem _root_.GlobalTheory.T.zalg_eq_adjoin_finite_capelli : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (b : ℕ), ∃ T : Finset (Module.End ℂ (Sm E b)), (∀ t ∈ T, ∃ (τ : E →+* ℂ) (u : ℂ), t = cap τ u) ∧ Zalg E b = Algebra.adjoin ℂ (T : Set (Module.End ℂ (Sm E b))) := by
  first | exact @GlobalTheory.CuspRep.zalg_eq_adjoin_finite_caps | exact GlobalTheory.CuspRep.zalg_eq_adjoin_finite_caps | (intros; apply GlobalTheory.CuspRep.zalg_eq_adjoin_finite_caps <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix

namespace GlobalTheory.IwasawaLast

theorem exists_unitary_lastRow {n : ℕ} (ℓ : Fin (n + 1) → ℂ) (hℓ : ℓ ≠ 0) :
    ∃ r : ℂ, r ≠ 0 ∧ ∃ k ∈ unitaryGroup (Fin (n + 1)) ℂ, ∀ l, ℓ l = r * k (Fin.last n) l := by
  set x : EuclideanSpace ℂ (Fin (n + 1)) := WithLp.toLp 2 (star ℓ) with hx
  have hx0 : x ≠ 0 := by
    intro h
    apply hℓ
    have : star ℓ = 0 := by
      have := congrArg WithLp.ofLp h
      simpa [hx] using this
    simpa using congrArg star this
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx0
  set w : EuclideanSpace ℂ (Fin (n + 1)) := ((‖x‖ : ℂ)⁻¹) • x with hw
  have hw1 : ‖w‖ = 1 := by
    rw [hw, norm_smul]
    simp [hn]
  have hon : Orthonormal ℂ (({Fin.last n} : Set (Fin (n + 1))).domRestrict (fun _ => w)) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Set.mem_singleton_iff] at hi hj
    subst hi; subst hj
    simp [Set.domRestrict, inner_self_eq_norm_sq_to_K, hw1]
  obtain ⟨b, hb⟩ := hon.exists_orthonormalBasis_extension_of_card_eq (by simp)
  have hbl : b (Fin.last n) = w := hb _ (Set.mem_singleton _)
  set M := (EuclideanSpace.basisFun (Fin (n + 1)) ℂ).toBasis.toMatrix b with hM
  have hMu : M ∈ unitaryGroup (Fin (n + 1)) ℂ :=
    OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary _ _
  refine ⟨(‖x‖ : ℂ), by exact_mod_cast hn, star M, ?_, ?_⟩
  · exact Unitary.star_mem hMu
  · intro l
    simp [hM, Matrix.star_apply, Module.Basis.toMatrix_apply, hbl, hw, hx]
    have hn' : ((‖WithLp.toLp 2 (star ℓ)‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [← mul_assoc, mul_inv_cancel₀ hn', one_mul]

end GlobalTheory.IwasawaLast

namespace GlobalTheory.IwasawaLast

theorem iwasawa_lastRow : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (y : GL (Fin (m + 1)) (Cinf E)), ∃ (p : GL (Fin (m + 1)) (Cinf E)) (ρ : (Cinf E)ˣ) (k : Kinf E (m + 1)), (∀ j, (p : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) (Fin.last m) j = if j = Fin.last m then 1 else 0) ∧ y = p * Units.map (Matrix.scalar (Fin (m + 1)) : Cinf E →+* Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)).toMonoidHom ρ * Unitary.toUnits k := by
  intro E _ _ _ m y
  set Y : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E) := (y : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) with hY
  set ℓ : InfinitePlace E → Fin (m + 1) → ℂ := fun v j => Y (Fin.last m) j v with hℓdef
  have hne : ∀ v, ℓ v ≠ 0 := by
    intro v h
    have hdet : IsUnit Y.det := (Matrix.isUnit_iff_isUnit_det Y).mp (Units.isUnit y)
    have hv : IsUnit (Y.det v) := (Pi.isUnit_iff.mp hdet) v
    have hmap : Y.det v = ((Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) v).mapMatrix Y).det :=
      RingHom.map_det (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) v) Y
    have h0 : ((Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) v).mapMatrix Y).det = 0 :=
      Matrix.det_eq_zero_of_row_eq_zero (Fin.last m) (fun j => by
        simpa [hℓdef] using congrFun h j)
    rw [hmap, h0] at hv
    exact not_isUnit_zero hv
  choose r hr kv hkv hℓ using fun v => exists_unitary_lastRow (ℓ v) (hne v)
  set K : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E) := Matrix.of fun i j v => kv v i j with hKdef
  have hK : K ∈ unitaryGroup (Fin (m + 1)) (Cinf E) := by
    rw [mem_unitaryGroup_iff]
    ext i j v
    have := congrFun (congrFun (mem_unitaryGroup_iff.mp (hkv v)) i) j
    by_cases hij : i = j <;> simp [hKdef, Matrix.mul_apply, Finset.sum_apply, Matrix.star_apply, Matrix.one_apply, hij] at this ⊢ <;> exact this
  have hρ : IsUnit (fun v => r v : Cinf E) := Pi.isUnit_iff.mpr fun v => (hr v).isUnit
  refine ⟨y * (Unitary.toUnits (⟨K, hK⟩ : Kinf E (m + 1)))⁻¹ *
      (Units.map (Matrix.scalar (Fin (m + 1)) : Cinf E →+* Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)).toMonoidHom hρ.unit)⁻¹,
    hρ.unit, ⟨K, hK⟩, ?_, by group⟩
  intro j
  ext v
  have hinv : (((Unitary.toUnits (⟨K, hK⟩ : Kinf E (m + 1)))⁻¹ : GL (Fin (m + 1)) (Cinf E)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) = star K := rfl
  have hρv : ((hρ.unit⁻¹ : (Cinf E)ˣ) : Cinf E) v = (r v)⁻¹ := by
    have h1 := congrFun hρ.unit.inv_mul v
    simp only [Units.val_mul, Pi.mul_apply, IsUnit.unit_spec, Units.val_one, Pi.one_apply] at h1
    exact eq_inv_of_mul_eq_one_left h1
  have hrow : ∀ l, Y (Fin.last m) l v = r v * kv v (Fin.last m) l := fun l => hℓ v l
  have hu := congrFun (congrFun (mem_unitaryGroup_iff.mp (hkv v)) (Fin.last m)) j
  simp only [Units.val_mul, Units.coe_map_inv, MonoidHom.coe_coe, hinv]
  rw [← hY]
  show (Y * star K * Matrix.scalar (Fin (m + 1)) ((hρ.unit⁻¹ : (Cinf E)ˣ) : Cinf E)) (Fin.last m) j v = _
  rw [Matrix.scalar_apply, Matrix.mul_diagonal]
  simp only [Matrix.scalar_apply, Matrix.mul_diagonal, Pi.mul_apply, hρv, Matrix.mul_apply, Finset.sum_apply, hrow, Matrix.star_apply, Pi.star_apply, hKdef, Matrix.of_apply] at hu ⊢
  have hs : ∑ x, r v * kv v (Fin.last m) x * star (kv v j x) = r v * ∑ x, kv v (Fin.last m) x * star (kv v j x) := by
    rw [Finset.mul_sum]; simp [mul_assoc]
  rw [hs, hu, Matrix.one_apply]
  by_cases hj : j = Fin.last m
  · subst hj; simp [hr v]
  · simp [hj, Ne.symm hj]

end GlobalTheory.IwasawaLast
end

section

open NumberField GlobalTheory.CuspRep

namespace GlobalTheory.CuspRep.KFin

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem cptRep_lie (k : Kinf E a) (X : Lie E a) (ψ : Sm E a) :
    cptRep E a k (lie E a X ψ) =
      lie E a (toL ((Unitary.toUnits k).val * Matrix.of X * (Unitary.toUnits k)⁻¹.val)) (cptRep E a k ψ) := by
  set y : GL (Fin a) (Cinf E) := Unitary.toUnits k with hy
  set Z : Lie E a := toL (y.val * Matrix.of X * y⁻¹.val) with hZ
  refine Subtype.ext (funext fun g => ?_)
  change lieD X ψ.1 (g * infGL E a y) = lieD Z (fun x => ψ.1 (x * infGL E a y)) g
  rw [← chart_val (lieD X ψ.1) g y, chart_lieD ψ.2 X g (val_mem_invSet y), lieD, chart_rt_inf]
  have e1 : rmul (toL y.val) (oneL E a) = toL y.val := one_mul (Matrix.of (toL y.val))
  rw [fderiv_comp _ (by rw [e1]; exact (contDiffAt_chart ψ.2 g (val_mem_invSet y)).differentiableAt (by simp))
    (rmul (toL y.val)).differentiableAt, ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply, e1]
  congr 1
  change (y.val : Matrix (Fin a) (Fin a) (Cinf E)) * Matrix.of X = (y.val * Matrix.of X * y⁻¹.val) * (y.val : Matrix (Fin a) (Fin a) (Cinf E))
  rw [mul_assoc, Units.inv_mul, mul_one]

theorem kfin_lie (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (X : Lie E a) (φ : Sm E a)
    (hφ : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E a k φ))) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E a k (lie E a X φ))) := by
  set V := Submodule.span ℂ (Set.range fun k => cptRep E a k φ)
  let b := Module.finBasis ℝ (Lie E a)
  refine Submodule.finiteDimensional_of_le (S₂ := ⨆ i, V.map (lie E a (b i))) (Submodule.span_le.2 ?_)
  rintro _ ⟨k, rfl⟩
  rw [SetLike.mem_coe]
  change cptRep E a k (lie E a X φ) ∈ _

  rw [cptRep_lie, ← b.sum_repr (toL _), map_sum, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [map_smul, LinearMap.smul_apply]
  exact Submodule.smul_of_tower_mem _ _ (Submodule.mem_iSup_of_mem i
    (Submodule.mem_map_of_mem (Submodule.subset_span ⟨k, rfl⟩)))

end GlobalTheory.CuspRep.KFin
end

section


theorem _root_.GlobalTheory.T.exists_algEquiv_lift_residue_padicAlgCl : ∀ (l : ℕ) [Fact l.Prime] (L : IntermediateField ℚ_[l] (PadicAlgCl l)) (φ : GlobalTheory.ZJ.kb l ≃+* GlobalTheory.ZJ.kb l), (∀ x : GlobalTheory.ZJ.OO l, (x : PadicAlgCl l) ∈ L → φ (IsLocalRing.residue (GlobalTheory.ZJ.OO l) x) = IsLocalRing.residue (GlobalTheory.ZJ.OO l) x) → ∃ g : PadicAlgCl l ≃ₐ[L] PadicAlgCl l, ∀ x y : GlobalTheory.ZJ.OO l, IsLocalRing.residue (GlobalTheory.ZJ.OO l) y = φ (IsLocalRing.residue (GlobalTheory.ZJ.OO l) x) → ‖g (x : PadicAlgCl l) - y‖ < 1 := by
  first | exact @GlobalTheory.ZJ.exists_algEquiv_lift_residue | exact GlobalTheory.ZJ.exists_algEquiv_lift_residue | (intros; apply GlobalTheory.ZJ.exists_algEquiv_lift_residue <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.ZH

theorem _root_.GlobalTheory.T.exists_nonempty_isIso_morphismRestrict_of_isHom_id : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (Y M : RatModel o Ω) (q : Y.Z ⟶ M.Z), M.IsHom Y (AlgHom.id o Ω) q → ∃ U : M.Z.Opens, (U : Set M.Z).Nonempty ∧ IsIso (q ∣_ U) := by
  first | exact @GlobalTheory.ZH.RatModel.exists_isIso_morphismRestrict_of_isHom_id | exact GlobalTheory.ZH.RatModel.exists_isIso_morphismRestrict_of_isHom_id | (intros; apply GlobalTheory.ZH.RatModel.exists_isIso_morphismRestrict_of_isHom_id <;> assumption)
end
