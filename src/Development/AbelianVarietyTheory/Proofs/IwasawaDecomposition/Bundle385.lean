module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle253
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle218
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle325
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugateEmbApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle003
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPlaceHeckeDoubleCosetsInverseRepsLabel
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle306
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle358
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle306
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle132
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle307
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle309
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle222
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSStageUnconditional
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle290
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle315
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle360
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle359
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle361
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle015
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPrinCongOfSm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle334

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Top.DsLow

theorem dimV_cast {n n' : ℕ} (h : n = n') (x : Fin n' → ℝ) :
    StandardLattice.dimV (fun i : Fin n => x (Fin.cast h i)) = StandardLattice.dimV x := by
  subst h; rfl

theorem trueDsig_eq_dimV (R : Ranks) (p : HCParam R) :
    Vol.trueDsig R p =
      StandardLattice.dimV (Fin.append (fun i => ((p.v i : ℚ) : ℝ)) (fun j => -((p.b j : ℚ) : ℝ))) := by
  have hk := R.m_add_three_le_k
  have hd : 2 * R.rS + R.k + 1 = R.k - 1 + R.m := by
    rw [Formalism.MainNotions.S.dimS_eq R]; simp only [Ranks.r]; omega
  unfold Vol.trueDsig
  rw [← StandardLattice.dimV_eq_fdegHC _ (Vol.lamSH_isHCParam R p).1, ← dimV_cast hd]
  congr 1
  funext a
  have key : ∀ (c : Fin (R.k - 1 + R.m)) (d : Fin R.r), d.val = c.val → Formalism.MainNotions.S.lamS R p d =
      Fin.append (fun i => ((p.v i : ℚ) : ℝ)) (fun j => -((p.b j : ℚ) : ℝ)) c := by
    intro c d hcd
    unfold Formalism.MainNotions.S.lamS
    induction c using Fin.addCases with
    | left i =>
      have hi : d.val = i.val := hcd
      have h1 : d.val < R.k - 1 := hi ▸ i.2
      rw [Fin.append_left, dite_eq_left h1]
      have e : (⟨d.val, h1⟩ : Fin (R.k - 1)) = i := Fin.ext hi
      rw [e]
    | right j =>
      have hj : d.val = R.k - 1 + j.val := hcd
      have h1 : ¬ d.val < R.k - 1 := by omega
      have h2 : d.val - (R.k - 1) < R.m := by have := j.2; omega
      rw [Fin.append_right, dite_eq_right h1, dite_eq_left h2]
      have e : (⟨d.val - (R.k - 1), h2⟩ : Fin R.m) = j := Fin.ext (by simp only; omega)
      rw [e]
  exact key _ _ rfl

theorem idxRowLoc_pos (g k m : ℕ) (hg : g.Prime) : 0 < StandardLattice.idxRowLoc g k m := by
  haveI : NeZero g := ⟨hg.ne_zero⟩
  unfold StandardLattice.idxRowLoc StandardLattice.idxLoc
  haveI : Nonempty {A : GL (Fin (k + m - 1)) (ZMod g) //
      StandardLattice.IsRowLev k (m / 2 - 1) (A : Matrix (Fin (k + m - 1)) (Fin (k + m - 1)) (ZMod g))} := by
    refine ⟨⟨1, ?_, ?_, ?_, ?_⟩⟩
    · intro i j h
      have : i ≠ j := by rintro rfl; exact lt_irrefl _ h
      simp [Matrix.one_apply_ne this]
    · intro i; simp
    · intro i j _ h
      simp [Matrix.one_apply_ne h.ne']
    · intro i j _ h _
      simp [Matrix.one_apply_ne h]
  apply div_pos
  · exact_mod_cast Nat.card_pos
  · exact_mod_cast Nat.card_pos

theorem DsP_pos_and_lower : ∀ P : PreCh, 0 < DsP P ∧ (2 / 3 : ℝ) ^ P.R.f * (letI := P.H.cmStar; Formalism.HermitianLatticesTheory.mass (StandardLattice.stdForm P.H.E P.R.r) (StandardLattice.stdLat P.H.E P.R.r)) * (StandardLattice.idxRowLoc (P.H.g 0) P.R.k P.R.m ^ P.R.f * StandardLattice.idxRowLoc (P.H.g 1) P.R.k P.R.m ^ P.R.f) * ∏ τ : Tau P.R, StandardLattice.dimV (Fin.append (fun i => (((P.hcW P.u₀ τ).v i : ℚ) : ℝ)) (fun j => -(((P.hcW P.u₀ τ).b j : ℚ) : ℝ))) ≤ DsP P := by
  intro P
  have hm : 0 < (letI := P.H.cmStar; Formalism.HermitianLatticesTheory.mass (StandardLattice.stdForm P.H.E P.R.r) (StandardLattice.stdLat P.H.E P.R.r)) := by
    letI := P.H.cmStar
    show 0 < Formalism.HermitianLatticesTheory.mass (StandardLattice.stdForm P.H.E P.R.r) (StandardLattice.stdLat P.H.E P.R.r)
    rw [StandardLattice.standard_form_eq_telescope_form, StandardLattice.standard_lattice_eq_telescope_lattice]
    exact Formalism.HermitianLatticesTheory.massTelescope_std_pos P.H.E (host_cmData P.R P.H).cmUnram _
  have h0 := idxRowLoc_pos _ P.R.k P.R.m (P.H.g_prime 0)
  have h1 := idxRowLoc_pos _ P.R.k P.R.m (P.H.g_prime 1)
  have hp : 0 < ∏ τ : Tau P.R, Vol.trueDsig P.R (P.hcW P.u₀ τ) :=
    Finset.prod_pos fun τ _ => (Vol.lamSH_isHCParam_and_trueDsig_pos _ _).2
  have hD : 0 < DsP P := by
    unfold DsP
    exact mul_pos (mul_pos hm (mul_pos (pow_pos h0 _) (pow_pos h1 _))) hp
  refine ⟨hD, ?_⟩
  have hc : (2 / 3 : ℝ) ^ P.R.f ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have he : ∏ τ : Tau P.R, StandardLattice.dimV (Fin.append (fun i => (((P.hcW P.u₀ τ).v i : ℚ) : ℝ))
      (fun j => -(((P.hcW P.u₀ τ).b j : ℚ) : ℝ))) = ∏ τ : Tau P.R, Vol.trueDsig P.R (P.hcW P.u₀ τ) :=
    Finset.prod_congr rfl fun τ _ => (trueDsig_eq_dimV _ _).symm
  rw [he]
  calc _ = (2 / 3 : ℝ) ^ P.R.f * DsP P := by unfold DsP; ring
    _ ≤ DsP P := mul_le_of_le_one_left hD.le hc

end GlobalTheory.Mem.Top.DsLow
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Col2

namespace JetEx

theorem hasLetters_of_over {K : Ctx} {P : Pre} (h : K.Over P) : StagesInhab.HasLetters P := by
  obtain ⟨sp, hT, hY, hA, hV, hz, rfl, -⟩ := h
  have hx : 0 < K.s.x := zero_lt_one.trans K.s.one_lt_alt
  refine ⟨(Delv K.s K.cD : ℚ), K.c, Nat.cast_pos.2 (Nat.ceil_pos.2 (Real.rpow_pos_of_pos hx _)), K.ok.inj,
    fun w τ l hl => ?_, K.ok.code⟩
  have h1 := (K.ok.hc w).1 τ
  change l + 1 < K.P.R.k - 1 at hl
  show (K.P.hcW w τ).v ⟨l, by omega⟩ - (K.P.hcW w τ).v ⟨l + 1, hl⟩ = _
  rw [h1, h1, show K.P.R.k - 2 - l = K.P.R.k - 2 - (l + 1) + 1 by omega]
  push_cast
  ring

end JetEx

end GlobalTheory.Mem.Col2

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

namespace GlobalTheory.Mem.BaseEnl

open GlobalTheory.Mem.BaseExt

section map

variable {L L' : Type} [Field L] [Field L'] [CharZero L] [CharZero L'] (ι : L →ₐ[ℚ] L')
  (K : IntermediateField ℚ L)

def toMap : K →+* K.map ι := (K.equivMap ι).toRingEquiv.toRingHom

theorem coe_toMap (x : K) : (toMap ι K x : L') = ι x := rfl

theorem toMap_surj : Function.Surjective (toMap ι K) := (K.equivMap ι).surjective

theorem image_map {E : Type} [Field E] (𝔞 : Ideal (𝓞 E)) (e : E → L) :
    extend (toMap ι K) (Submodule.span (𝓞 K) {x : K | ∃ a ∈ 𝔞, (x : L) = e (a : E)}) =
      Submodule.span (𝓞 (K.map ι)) {x : K.map ι | ∃ a ∈ 𝔞, (x : L') = ι (e (a : E))} := by
  rw [extend_span]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨a, ha, hy⟩, rfl⟩
    exact ⟨a, ha, by rw [coe_toMap, hy]⟩
  · rintro ⟨a, ha, hx⟩
    obtain ⟨y, rfl⟩ := toMap_surj ι K x
    exact ⟨y, ⟨a, ha, ι.injective hx⟩, rfl⟩

end map

theorem exists_enl : ∀ (B : Base) (S : Finset ℂ), (∀ z ∈ S, IsAlgebraic ℚ z) →
    ∃ B' : Base, Enl B B' ∧ ∀ z ∈ S, ∃ x : B'.LL, B'.embLL x = z := by
  classical
  intro B S h
  obtain ⟨SE, hSE, hE⟩ := exists_gens B.LL
  obtain ⟨K, hfd, hKgal, hS, -, hconj⟩ := GlobalTheory.exists_galois_subfield_conj_stable (S ∪ SE) (by
    intro z hz
    rcases Finset.mem_union.1 hz with hz | hz
    exacts [h z hz, hSE z hz])
  have hEK := hE K (fun z hz => hS z (Finset.mem_union_right _ hz)) B.embLL
  have : NumberField K := {}
  let ι : B.LL →ₐ[ℚ] K := (B.embLL.codRestrict K hEK).toRatAlgHom
  have hι : ∀ x, K.val (ι x) = B.embLL x := fun _ => rfl
  have tr : ∀ (F : IntermediateField ℚ B.LL) (w : ℂ), (∃ z ∈ F, B.embLL z = w) →
      ∃ z ∈ F.map ι, K.val z = w := by
    rintro F w ⟨z, hz, rfl⟩
    exact ⟨ι z, ⟨z, hz, rfl⟩, rfl⟩
  have im : ∀ F : IntermediateField ℚ B.LL,
      (K.val : K →+* ℂ) '' (F.map ι : Set K) = B.embLL '' (F : Set B.LL) := by
    intro F
    ext w
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨z, hz, rfl⟩
    · exact tr F w
  have hg0 := B.coeffGaloisSubfield_isGalois
  let f := toMap ι B.Ks
  refine ⟨{ toPre := B.toPre
            LL := K
            starLL := starOf K hconj
            embLL := K.val
            starLL_cx := fun _ => rfl
            embE := (ι : B.LL →+* K).comp B.embE
            embE_φ₀ := by rw [← B.embE_φ₀]; rfl
            LL0 := B.LL0.map ι
            coeffGaloisSubfield_isGalois := @IsGalois.of_algEquiv ℚ B.LL0 _ _ (B.LL0.map ι) _ _ _ hg0 (B.LL0.equivMap ι)
            Ks := B.Ks.map ι
            Ks_le := IntermediateField.map_mono ι B.Ks_le
            E_le_Ks := fun x => ⟨B.embE x, B.E_le_Ks x, rfl⟩
            roots_Ks := fun N hN => tr _ _ (B.roots_Ks N hN)
            roots_Ks' := fun N hN => tr _ _ (B.roots_Ks' N hN)
            capit := ?_
            kPsi := ?_
            rootOfUnity_eightQ_mem_coeffGaloisSubfield := tr _ _ B.rootOfUnity_eightQ_mem_coeffGaloisSubfield
            roots_LL := fun u => ?_ }, ⟨rfl, im _, im _, ?_⟩, ?_⟩
  · intro 𝔞
    obtain ⟨β, hsp⟩ := B.capit 𝔞
    refine ⟨f β, ?_⟩
    have h := congrArg (extend f) hsp
    rw [extend_span, Set.image_singleton] at h
    exact h.trans (image_map ι B.Ks 𝔞 B.embE)
  · intro j hj1 hj 𝔞 h𝔞
    obtain ⟨β, hβ, hsp, hn⟩ := B.kPsi j hj1 hj 𝔞 h𝔞
    refine ⟨f β, (map_ne_zero f).2 hβ, ?_, fun σ => hn (σ.comp f)⟩
    have h := congrArg (extend f) hsp
    rw [extend_span, Set.image_singleton, map_prod] at h
    rw [h]
    refine Finset.prod_congr rfl fun g _ => ?_
    have e1 := image_map ι B.Ks 𝔞 (fun a => B.embE (B.host.sigmaOf g a))
    have e2 := image_map ι B.Ks 𝔞 (fun a => B.embE (B.host.sigmaOf g (B.host.conj a)))
    rw [map_mul, map_pow, map_pow]
    exact congrArg₂ (· * ·) (congrArg (· ^ (B.R.sigW j).1) e1) (congrArg (· ^ (B.R.sigW j).2) e2)
  · obtain ⟨z, hz⟩ := B.roots_LL u
    exact ⟨ι z, hz⟩
  · rintro _ ⟨z, rfl⟩
    exact ⟨ι z, rfl⟩
  · exact fun z hz => ⟨⟨z, hS z (Finset.mem_union_left _ hz)⟩, rfl⟩

end GlobalTheory.Mem.BaseEnl

end
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

noncomputable section

namespace GlobalTheory.InertSatake

def transport {G H : Type} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H] (P : G ≃ₜ* H)
    (σ : SmIrr G) : SmIrr H where
  V := σ.V
  ρ := σ.ρ.comp P.symm.toMulEquiv.toMonoidHom
  smooth v := (σ.smooth v).preimage P.symm.continuous
  irred := by
    obtain ⟨h0, h⟩ := (CuspRep.isIrreducible_iff _).1 σ.irred
    refine (CuspRep.isIrreducible_iff _).2 ⟨h0, fun W hW => h W fun g v hv => ?_⟩
    have := hW (P g) v hv
    change σ.ρ (P.symm (P g)) v ∈ W at this
    rwa [P.symm_apply_apply] at this

theorem transport_apply {G H : Type} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H] (P : G ≃ₜ* H)
    (σ : SmIrr G) (g : G) (v : σ.V) : (transport P σ).ρ (P g) v = σ.ρ g v := by
  change σ.ρ (P.symm (P g)) v = _
  rw [P.symm_apply_apply]

theorem isAdmissible_transport {G H : Type} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
    (P : G ≃ₜ* H) (σ : SmIrr G) (h : IsAdmissible σ.ρ) : IsAdmissible (transport P σ).ρ := by
  refine ⟨(transport P σ).smooth, fun K ho hc => ?_⟩
  let K' : Subgroup G := K.comap P.toMulEquiv.toMonoidHom
  show FiniteDimensional ℂ (fixed (σ.ρ.comp P.symm.toMulEquiv.toMonoidHom) K)
  have e : fixed (σ.ρ.comp P.symm.toMulEquiv.toMonoidHom) K = fixed σ.ρ K' := by
    ext x
    rw [GlobalTheory.LGrp.mem_fixed, GlobalTheory.LGrp.mem_fixed]
    constructor
    · intro hx k hk
      have := hx (P k) hk
      change σ.ρ (P.symm (P k)) x = x at this
      rwa [P.symm_apply_apply] at this
    · intro hx k hk
      exact hx (P.symm k) (by change P (P.symm k) ∈ K; rwa [P.apply_symm_apply])
  rw [e]
  refine h.2 K' (ho.preimage P.continuous) ?_
  have : (K' : Set G) = P.toHomeomorph ⁻¹' (K : Set H) := rfl
  rw [this]
  exact P.toHomeomorph.isCompact_preimage.2 hc

variable {L : Type} [Field L] [TopologicalSpace L] [IsTopologicalRing L] {n : ℕ}

def conjEquiv (s : L →+* L) (b : GL (Fin n) L) (hb : cT s b.1 * 1 * b.1 = antiJ L n) :
    UJ s (1 : Matrix (Fin n) (Fin n) L) ≃ₜ* GU s n where
  toFun g := ⟨b⁻¹ * g * b, GlobalTheory.InertDoubleCoset.conj_mem_UJ s hb g.2⟩
  invFun h := ⟨b * h * b⁻¹, by simpa using GlobalTheory.InertDoubleCoset.conj_mem_UJ s (GlobalTheory.InertDoubleCoset.inv_frame s hb) h.2⟩
  left_inv g := Subtype.ext (by simp [mul_assoc])
  right_inv h := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const

end GlobalTheory.InertSatake


open GlobalTheory.InertSatake in
theorem GlobalTheory.InertSatake.sph_iff_isSat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AU E n)
    (w : HeightOneSpectrum (𝓞 E)), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal → ¬ IsSplitAt w →
    (π.Sph w ↔ ∃ α, π.IsSat w α) := by
  intro E _ _ _ n π w hun hns
  obtain ⟨π, rfl⟩ := AU.mk_surjective π
  show IsUnramU π.V w ↔ ∃ α, π.IsSat w α
  constructor
  · rintro ⟨φ, hφ, h0, hfix⟩
    obtain ⟨s, ϖ, q, hs, hU⟩ := GlobalTheory.T.unramified_nonsplit_exists_conj_involution_uniformiser E w hun hns
    obtain ⟨e, he⟩ := GlobalTheory.T.fixedPlace_unitaryLocalPoints_equiv_localUnitaryGroup E n w s hs hU.2.1
    obtain ⟨b, hbK, hb⟩ := GlobalTheory.LFun.InertChart.exists_congr_antiJ hU (one_mem (GlobalTheory.LFun.KGL w (n := n)))
      (by rw [Units.val_one, cT_one])
    let P : locU n w ≃ₜ* GU s n := e.trans (conjEquiv s b hb)
    have hP : ∀ x : locU n w, ((P x : GU s n) : GL (Fin n) (w.adicCompletion E)) = b⁻¹ * cLoc w x.1 * b := fun x => by
      change b⁻¹ * (e x : GL (Fin n) _) * b = _
      rw [he]
    obtain ⟨σ0, hadm, hcomp⟩ := GlobalTheory.T.exists_admissible_localComponent_definiteUnitary E n π w
    obtain ⟨r, -, -, hr⟩ := GlobalTheory.T.exists_continuous_retraction_onto_unitaryLocalPoints E n w
    obtain ⟨-, f, hf0, hfm, hf⟩ := hcomp
    let F : σ0.ρ.IntertwiningMap (π.rep.comp (locU n w).subtype) :=
      ⟨f.codRestrict _ hfm, fun x => LinearMap.ext fun v => Subtype.ext (hf x v)⟩
    have hF0 : F ≠ 0 := fun h => hf0 (LinearMap.ext fun v => by
      have := congrArg Subtype.val (DFunLike.congr_fun h v)
      exact this)
    have htop := (GlobalTheory.T.irreducibleRep_isotypic_of_centraliser_factor (UA E n) (locU n w) π.V σ0.V σ0.V π.rep (locU n w).subtype σ0.ρ σ0.ρ
      π.isIrreducible_rep σ0.irred σ0.irred (fun g => ⟨r g, fun y => hr g y⟩) F hF0).1
    obtain ⟨v, hv0, hv⟩ := GlobalTheory.CuspRep.LocSph.exists_fixed_of_mem_iSup (π.rep.comp (locU n w).subtype) σ0.ρ σ0.irred
      (fun i : σ0.ρ.IntertwiningMap (π.rep.comp (locU n w).subtype) => i.toLinearMap)
      (fun i g u => Representation.IntertwiningMap.isIntertwining _ _ i g u) {x | cLoc w x.1 ∈ GlobalTheory.LFun.KGL w (n := n)} ⟨φ, hφ⟩
      (fun h => h0 (congrArg Subtype.val h)) (fun k hk => Subtype.ext (hfix k.1 k.2 hk))
      (htop ▸ Submodule.mem_top)
    let σ1 := transport P σ0
    have hsph : GlobalTheory.LGrp.IsSpherical σ1.ρ (KU s n) := by
      refine (Submodule.ne_bot_iff _).2 ⟨v, GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_, hv0⟩
      obtain ⟨x, rfl⟩ := P.surjective k
      rw [transport_apply]
      refine hv x ?_
      have h1 : ((P x : GU s n) : GL (Fin n) (w.adicCompletion E)) ∈ GLint (Fin n) (intL (w.adicCompletion E)) :=
        (Set.ext_iff.1 (GlobalTheory.LFun.IntPtsUnitary.coe_KU s n) (P x)).1 hk
      have h2 : cLoc w x.1 = b * (P x : GL (Fin n) (w.adicCompletion E)) * b⁻¹ := by rw [hP]; group
      show cLoc w x.1 ∈ GlobalTheory.LFun.KGL w (n := n)
      rw [h2]
      exact mul_mem (mul_mem hbK h1) (inv_mem hbK)
    obtain ⟨α, hα⟩ := GlobalTheory.T.exists_satake_parameter_spherical_unramifiedUnitary E w ϖ s q n hU σ1.V σ1.ρ σ1.irred (isAdmissible_transport P σ0 hadm) hsph
    refine ⟨α, s, ϖ, q, hs, hU, b, hbK, by have h := hb; rw [Units.val_one, Matrix.mul_one] at h; exact h, P.toMulEquiv.toMonoidHom, hP, σ1,
      ⟨σ1.irred, f, hf0, hfm, fun x u => ?_⟩, hα⟩
    change f (σ0.ρ (P.symm (P x)) u) = _
    rw [P.symm_apply_apply]
    exact hf x u
  · rintro ⟨α, s, ϖ, q, hs, hU, b, hbK, hb, p, hp, σ, ⟨-, f, hf0, hfm, hf⟩, hsat⟩
    obtain ⟨e, he⟩ := GlobalTheory.T.fixedPlace_unitaryLocalPoints_equiv_localUnitaryGroup E n w s hs hU.2.1
    have hb1 : cT s b.1 * 1 * b.1 = antiJ _ n := by rwa [Matrix.mul_one]
    have hsurj : Function.Surjective p := fun g => by
      let P := e.trans (conjEquiv s b hb1)
      have hP : ((P (P.symm g) : GU s n) : GL (Fin n) (w.adicCompletion E)) =
          b⁻¹ * cLoc w (P.symm g).1 * b := by
        change b⁻¹ * (e _ : GL (Fin n) _) * b = _
        rw [he]
      refine ⟨P.symm g, Subtype.ext ?_⟩
      rw [hp, ← hP, P.apply_symm_apply]
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hsat.1
    have hfv : f v ≠ 0 := by
      intro h
      have hker := ((CuspRep.isIrreducible_iff _).1 σ.irred).2 (LinearMap.ker f) fun g u hu => by
        obtain ⟨x, rfl⟩ := hsurj g
        rw [LinearMap.mem_ker, hf, LinearMap.mem_ker.1 hu, map_zero]
      rcases hker with h1 | h1
      · have m : v ∈ LinearMap.ker f := LinearMap.mem_ker.2 h
        rw [h1] at m
        exact hv0 ((Submodule.mem_bot ℂ).1 m)
      · exact hf0 (LinearMap.ker_eq_top.1 h1)
    refine ⟨f v, hfm v, hfv, fun x hx hk => ?_⟩
    have hpk : p ⟨x, hx⟩ ∈ KU s n := by
      refine (Set.ext_iff.1 (GlobalTheory.LFun.IntPtsUnitary.coe_KU s n) _).2 ?_
      show ((p ⟨x, hx⟩ : GU s n) : GL (Fin n) (w.adicCompletion E)) ∈ GLint (Fin n) (intL _)
      rw [hp]
      exact mul_mem (mul_mem (inv_mem hbK) hk) hbK
    refine (hf ⟨x, hx⟩ v).symm.trans ?_
    rw [GlobalTheory.LGrp.mem_fixed.1 hv _ hpk]
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df
attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem _root_.GlobalTheory.T.stepZeroColumns_classSumForm_posDef : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (hX : B.fields.Ok), SpectralModel.ColsPos (I.cols l) := by
  first | exact @GlobalTheory.Mem.Df.cols_pos | exact GlobalTheory.Mem.Df.cols_pos | (intros; apply GlobalTheory.Mem.Df.cols_pos <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC



theorem laws_of_ok : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → I.Laws := by
  intro B X I h
  have hch := GlobalTheory.T.trueColumn_chains_satisfy_conditions I h
  have hlev := GlobalTheory.T.levelPrimeData_ok_of_trueColumnChoices I h
  have hper := GlobalTheory.T.trueColumns_periodMapDatum_ok_and_over_levelPrime I h
  have hall := fun u a => laws_all (I.chIn u a) (I.atIn u a) B.fields.emb B.embLL (B.hcW u) (base_fOk B) (hch u a).1 (hlev u a)
    (I.perIn u a) (hper u a).1 B.places
  exact
    { pr := (base_fields_primes_ok B X).2.1
      ch := fun u a => (hch u a).1
      lev := hlev
      per := fun u a => (hper u a).1
      ovr := fun u a => (hper u a).2
      atL := fun u a => (hall u a).1
      fmL := fun u a => (hall u a).2
      xi0 := h.trueColumnChoices_heckeChar_reference_eq_one
      idx0 := fun a => (hch B.u₀ a).2.1
      bij0 := fun u a b => (GlobalTheory.T.cl0_bijective_and_deco_eq I h u a b).1
      lat := fun u a => (hch u a).2.2 }

end GlobalTheory.Mem.Col2.TC
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lastStep_tuple_group_classes_coordinates : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (u : B.Word) (a : I.ι), (∀ c : (I.stp u a B.R.m).Cl, ∃ e : (I.stp u a B.R.m).G c.1 ≃ (UF B.host.E (B.R.N B.R.m) × ((I.Tp a).levG B.R.m).grp × ((I.Tp a).levQ B.R.m).grp), ∀ κ : (I.stp u a B.R.m).G c.1, (e κ).1 = κ.1 ∧ (I.stp u a B.R.m).gam c.1 κ = ufGL B.host.E (B.R.N B.R.m) (e κ).1 ∧ (I.stp u a B.R.m).chr c.1 κ = ((I.Tp a).levG B.R.m).chr (e κ).2.1 * ((I.Tp a).levQ B.R.m).chr (e κ).2.2 ∧ ((I.stp u a B.R.m).act c.1 κ ((I.stp u a B.R.m).rep c)).1.1 = (((e κ).1, (e κ).2.1.1, (e κ).2.2.1) : UF B.host.E (B.R.N B.R.m) × GLG (E := B.host.E) (n := B.R.N B.R.m) (SG := (B.primes X).vGs) × GLQ B.host.E (B.R.N B.R.m) (I.Q a)) • ((I.stp u a B.R.m).rep c).1.1 ∧ cosetIn ((I.stp u a B.R.m).act c.1 κ ((I.stp u a B.R.m).rep c)) = cosetIn ((I.stp u a B.R.m).rep c) ∧ (((I.stp u a B.R.m).act c.1 κ ((I.stp u a B.R.m).rep c)).1.1 = ((I.stp u a B.R.m).rep c).1.1 → (I.stp u a B.R.m).act c.1 κ ((I.stp u a B.R.m).rep c) = (I.stp u a B.R.m).rep c)) ∧ (∀ (c c' : (I.stp u a B.R.m).Cl) (γ : UF B.host.E (B.R.N B.R.m)) (h : ((I.Tp a).levG B.R.m).grp) (θ : ((I.Tp a).levQ B.R.m).grp), ((γ, h.1, θ.1) : UF B.host.E (B.R.N B.R.m) × GLG (E := B.host.E) (n := B.R.N B.R.m) (SG := (B.primes X).vGs) × GLQ B.host.E (B.R.N B.R.m) (I.Q a)) • ((I.stp u a B.R.m).rep c).1.1 = ((I.stp u a B.R.m).rep c').1.1 → c = c') ∧ (∀ p : DecoF B.host.E (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs (I.Q a), ∃ (c : (I.stp u a B.R.m).Cl) (γ : UF B.host.E (B.R.N B.R.m)) (h : ((I.Tp a).levG B.R.m).grp) (θ : ((I.Tp a).levQ B.R.m).grp), ((γ, h.1, θ.1) : UF B.host.E (B.R.N B.R.m) × GLG (E := B.host.E) (n := B.R.N B.R.m) (SG := (B.primes X).vGs) × GLQ B.host.E (B.R.N B.R.m) (I.Q a)) • ((I.stp u a B.R.m).rep c).1.1 = p) ∧ Nonempty (I.stp u a B.R.m).Cl := by
  intro B X I u a
  exact GlobalTheory.stpTop_groupClasses I u a
end
