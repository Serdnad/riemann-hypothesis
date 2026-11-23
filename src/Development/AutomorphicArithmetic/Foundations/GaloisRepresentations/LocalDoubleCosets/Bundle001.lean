module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.TracePow
import GroundTheory.AutomorphicForms.LocallyProfinite
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel Matrix MeasureTheory UpperTheory.ConvolutionTheory.Loc MulAction UpperTheory.Gal.LocD

theorem UpperTheory.Gal.LocD.stabSub :
    StabSub := by
  intro H _ _ _ _ _ _ τ p hp hτ hper L hL
  obtain ⟨K, hKc, hKL⟩ := GroundTheory.Automorphic.exists_openSubgroup_isCompact_subset
    (hL.mem_nhds L.one_mem)
  let L₀ : Subgroup H :=
    { carrier := {l | ∀ i < p, τ^[i] l ∈ K}
      one_mem' := fun i _ => by rw [iterate_map_one]; exact K.one_mem
      mul_mem' := fun ha hb i hi => by
        rw [iterate_map_mul]; exact K.mul_mem (ha i hi) (hb i hi)
      inv_mem' := fun ha i hi => by
        rw [iterate_map_inv]; exact K.inv_mem (ha i hi) }
  have hset : (L₀ : Set H) = ⋂ i ∈ {i : ℕ | i < p}, τ^[i] ⁻¹' (K : Set H) := by
    ext l; simp [L₀]
  have hopen : IsOpen (L₀ : Set H) := by
    rw [hset]
    exact (Set.finite_lt_nat p).isOpen_biInter
      (fun i _ => K.isOpen.preimage (hτ.iterate i))
  have hsub : (L₀ : Set H) ⊆ K := fun l hl => by
    have := hl 0 hp
    simpa using this
  refine ⟨L₀, hKc.of_isClosed_subset (L₀.isClosed_of_isOpen hopen) hsub, hopen,
    fun l hl => hKL (hsub hl), fun l => ?_⟩
  show (∀ i < p, τ^[i] (τ l) ∈ K) ↔ ∀ i < p, τ^[i] l ∈ K
  constructor
  · intro h i hi
    rcases i with _ | j
    · have h1 := h (p - 1) (by omega)
      rw [← Function.iterate_succ_apply, Nat.succ_eq_add_one, Nat.sub_add_cancel hp,
        hper] at h1
      simpa using h1
    · rw [Function.iterate_succ_apply]
      exact h j (by omega)
  · intro h i hi
    rw [← Function.iterate_succ_apply]
    by_cases hlt : i + 1 < p
    · exact h (i + 1) hlt
    · have hip : i + 1 = p := by omega
      rw [Nat.succ_eq_add_one, hip, hper]
      simpa using h 0 hp
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel Matrix UpperTheory.ConvolutionTheory.Loc

namespace UpperTheory.Gal.LocD

section

variable {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] {n : ℕ}

private def dg (E : Type) [Field E] (n : ℕ) : borel E (Fin n) →* (Fin n → Eˣ) :=
  (leviTorus E (Fin n)).symm.toMonoidHom.comp (leviProj E (points (Fin n)))

private theorem dg_val (b : borel E (Fin n)) (i : Fin n) :
    ((dg E n b i : Eˣ) : E) = ((b : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i i := by
  show (GeneralLinearGroup.det (leviProj E (points (Fin n)) b i) : E) = _
  rw [GeneralLinearGroup.val_det_apply, Matrix.det_unique]
  exact leviProj_apply E (points (Fin n)) b i _ _

private theorem absPow_map (σ : E ≃+* E) (hσ : Isom σ) (s : ℂ) (x : Eˣ) :
    absPow E s (Units.map (σ : E →* E) x) = absPow E s x := by
  have hv : valuation E ((Units.map (σ : E →* E) x * x⁻¹ : Eˣ) : E) = 1 := by
    have hx : valuation E (x : E) ≠ 0 := by simp
    simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, Units.val_inv_eq_inv_val, map_mul, map_inv₀]
    rw [hσ]
    exact mul_inv_cancel₀ hx
  have h1 := isUnram_absPow E s _ hv
  have h2 : Units.map (σ : E →* E) x = (Units.map (σ : E →* E) x * x⁻¹) * x := by group
  rw [h2, map_mul, h1, one_mul]

private def dl (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) :
    borel E (Fin n) →* ℂˣ :=
  (deltaHalf E (fun _ : Fin n => Unit)).comp (leviProj E (points (Fin n)))

private theorem dl_eq (b : borel E (Fin n)) :
    dl E n b = ∏ i, absPow E ((modExp (fun _ : Fin n => Unit) i : ℂ) / 2) (dg E n b i) :=
  deltaHalf_apply E _

end

theorem toBorel : ToBorel := by
  intro E _ _ _ _ n σ hσ V _ _ π μ hμ l hl
  refine ⟨dl E n * μ.comp (dg E n), ?_, ?_⟩
  · intro b b' hbb'
    have hd : dg E n b' = fun i => Units.map (σ : E →* E) (dg E n b i) := by
      funext i
      ext
      rw [dg_val, hbb', Units.coe_map, dg_val]
      simp only [sg, Matrix.GeneralLinearGroup.map_apply]
      rfl
    simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, dl_eq, hd, hμ, absPow_map σ hσ]
  · intro b v
    obtain ⟨u, hu, hbu⟩ := exists_levi_mul_unip E (points (Fin n)) b
    have hq : (Submodule.Quotient.mk (π u v) : Jacquet π (unipB E (Fin n))) = Submodule.Quotient.mk v := by
      rw [Submodule.Quotient.eq]
      apply Submodule.subset_span
      exact ⟨⟨u, hu⟩, v, by simp⟩
    have hL : leviTorus E (Fin n) (dg E n b) = leviProj E (points (Fin n)) b :=
      MulEquiv.apply_symm_apply _ _
    have ht : jacB π (dg E n b) (Submodule.Quotient.mk (π u v))
        = jac (points (Fin n)) π (leviProj E (points (Fin n)) b) (Submodule.Quotient.mk (π u v)) := by
      show jac (points (Fin n)) π (leviTorus E (Fin n) (dg E n b)) _ = _
      exact congrArg (fun g => jac (points (Fin n)) π g (Submodule.Quotient.mk (π u v))) hL
    have h2 : l (jacB π (dg E n b) (Submodule.Quotient.mk (π u v)))
        = (((deltaHalf E (fun _ : Fin n => Unit) (leviProj E (points (Fin n)) b))⁻¹ : ℂˣ) : ℂ)
          * l (Submodule.Quotient.mk ((π (leviEmb E (points (Fin n)) (leviProj E (points (Fin n)) b))) (π u v))) := by
      rw [ht, jac_mk]
      exact map_smul l _ _
    have hX : l (Submodule.Quotient.mk ((π (leviEmb E (points (Fin n)) (leviProj E (points (Fin n)) b))) (π u v)) : Jacquet π (unipB E (Fin n)))
        = ((deltaHalf E (fun _ : Fin n => Unit) (leviProj E (points (Fin n)) b) : ℂˣ) : ℂ)
          * ((μ (dg E n b) : ℂ) * l (Submodule.Quotient.mk v)) := by
      rw [← hq, ← hl, h2, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
    rw [hbu, map_mul, Module.End.mul_apply, hX, MonoidHom.mul_apply, MonoidHom.comp_apply, Units.val_mul, mul_assoc]
    rfl

end UpperTheory.Gal.LocD

end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel Matrix MeasureTheory UpperTheory.ConvolutionTheory.Loc MulAction UpperTheory.Gal.LocD

theorem UpperTheory.Gal.LocD.prMem :
    PrMem := by
  intro G _ _ _ _ _ _ _ B hB _ _ μ _ χ hker
  haveI : SecondCountableTopology B := TopologicalSpace.Subtype.secondCountableTopology _
  have hχc : Continuous (fun x : B => (χ x : ℂ)) := by
    have := continuous_of_continuousAt_one ((Units.coeHom ℂ).comp χ) ?_
    · exact this
    · refine (continuousAt_const (y := (1 : ℂ))).congr ?_
      filter_upwards [hker.mem_nhds (one_mem χ.ker)] with x hx
      have hx' : χ x = 1 := MonoidHom.mem_ker.mp hx
      simp [hx']
  have hint : ∀ f ∈ Cc G, ∀ g : G,
      Integrable (fun x : B => (χ x : ℂ) * f ((x : G)⁻¹ * g)) μ := by
    intro f hf g
    rw [GroundTheory.Automorphic.mem_locallyConstantCompactSupport] at hf
    obtain ⟨hlc, hcs⟩ := hf
    have hemb : Topology.IsClosedEmbedding (fun x : B => (x : G)⁻¹ * g) :=
      ((Homeomorph.inv G).trans (Homeomorph.mulRight g)).isClosedEmbedding.comp
        hB.isClosedEmbedding_subtypeVal
    have hcs' : HasCompactSupport (fun x : B => f ((x : G)⁻¹ * g)) :=
      hcs.comp_isClosedEmbedding hemb
    exact Continuous.integrable_of_hasCompactSupport
      (hχc.mul (hlc.continuous.comp hemb.continuous)) hcs'.mul_left
  refine ⟨fun f hf => ?_, fun f hf f' hf' => ?_⟩
  · rw [mem_indF]
    constructor
    · intro b g
      simp only [pr]
      rw [← integral_mul_left_eq_self _ b, ← integral_const_mul]
      congr 1
      ext x
      simp only [map_mul, Units.val_mul, Subgroup.coe_mul, _root_.mul_inv_rev, mul_assoc,
        inv_mul_cancel_left]
    · obtain ⟨K, -, hK⟩ := GroundTheory.Automorphic.exists_forall_mul_right hf
      refine ⟨(K : Subgroup G), K.isOpen, fun k hk g => ?_⟩
      simp only [pr]
      congr 1
      ext x
      rw [← mul_assoc, hK _ _ hk]
  · funext g
    simp only [pr, Pi.add_apply, mul_add]
    exact integral_add (hint f hf g) (hint f' hf' g)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel Matrix MeasureTheory UpperTheory.ConvolutionTheory.Loc MulAction UpperTheory.Gal.LocD

theorem UpperTheory.Gal.LocD.etaEx :
    EtaEx := by
  intro G _ _ _ _ _ _ B s p hp hper P κ hκ hs hB hne
  obtain ⟨f₀, hf₀, g₀, h0⟩ := hne
  obtain ⟨K, hK, hKf⟩ := GroundTheory.Automorphic.exists_forall_mul_left (R := ℂ) hf₀
  set e : B → ℂ := fun b => P (fun x => f₀ ((b : G)⁻¹ * x)) g₀ / P f₀ g₀ with he
  have hη : ∀ (b : B) (f : G → ℂ) (g : G), P (fun x => f ((b : G)⁻¹ * x)) g = e b * P f g := by
    intro b f g
    obtain ⟨c, hc⟩ := hB b
    have hc0 := hc f₀ g₀
    have : e b = c := by
      rw [he]; dsimp only; rw [hc0, mul_div_assoc, div_self h0, mul_one]
    rw [this, hc]
  have hpow : ∀ (n : ℕ) (f : G → ℂ) (g : G), P (f ∘ s^[n]) g = (κ : ℂ) ^ n * P f (s^[n] g) := by
    intro n
    induction n with
    | zero => intro f g; simp
    | succ n ih =>
      intro f g
      rw [Function.iterate_succ, ← Function.comp_assoc, hs, ih, Function.comp_apply, pow_succ]
      ring
  have hper' : s^[p] = id := funext hper
  have hκ1 : κ = 1 := by
    have h1 := hpow p f₀ g₀
    rw [hper', Function.comp_id, id] at h1
    have hk : (κ : ℂ) ^ p = 1 := by
      have := mul_right_cancel₀ h0 (h1.symm.trans (one_mul _).symm)
      exact this
    have hk' : κ ^ p = 1 := by exact_mod_cast hk
    exact (pow_eq_one_iff_of_nonneg hκ.le hp.ne').1 hk'
  have e1 : e 1 = 1 := by
    rw [he]; dsimp only; simp [div_self h0]
  have emul : ∀ b b' : B, e (b * b') = e b * e b' := by
    intro b b'
    have h := hη b (fun x => f₀ ((b' : G)⁻¹ * x)) g₀
    rw [hη b' f₀ g₀] at h
    have h2 : e (b * b') * P f₀ g₀ = e b * e b' * P f₀ g₀ := by
      rw [← hη, mul_assoc, ← h]
      congr 1
      funext x
      simp [mul_assoc]
    exact mul_right_cancel₀ h0 h2
  let η : B →* ℂ := { toFun := e, map_one' := e1, map_mul' := emul }
  refine ⟨hκ1, η, fun b f g => hη b f g, ⟨K, K.isOpen, fun b hb => ?_⟩, fun b b' hbb => ?_⟩
  · show e b = 1
    rw [he]
    dsimp only
    have hfix : (fun x => f₀ ((b : G)⁻¹ * x)) = f₀ :=
      funext fun x => hKf _ (K.inv_mem (by exact hb)) x
    rw [hfix, div_self h0]
  · show e b' = e b
    have hg1 : s (s^[p - 1] g₀) = g₀ := by
      rw [← Function.iterate_succ_apply' (f := s), Nat.succ_eq_add_one, Nat.sub_add_cancel hp,
        hper]
    have hA := hη b (f₀ ∘ s) (s^[p - 1] g₀)
    rw [hs, hg1] at hA
    have hfun : (fun x => (f₀ ∘ s) ((b : G)⁻¹ * x)) = (fun x => f₀ ((b' : G)⁻¹ * x)) ∘ s := by
      funext x
      simp [hbb, map_mul, map_inv]
    rw [hfun, hs, hg1, hη b' f₀ g₀] at hA
    have hκ0 : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
    have h3 : e b' * P f₀ g₀ = e b * P f₀ g₀ := by
      have := mul_left_cancel₀ hκ0 (hA.trans (by ring : e b * (↑κ * P f₀ g₀) = ↑κ * (e b * P f₀ g₀)))
      exact this
    exact mul_right_cancel₀ h0 h3
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel Matrix MeasureTheory UpperTheory.ConvolutionTheory.Loc MulAction UpperTheory.Gal.LocD

private theorem mem_Cc_mul_right {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {f : G → ℂ} (hf : f ∈ Cc G) (u : G) : (fun x => f (x * u)) ∈ Cc G := by
  rw [GroundTheory.Automorphic.mem_locallyConstantCompactSupport] at hf ⊢
  refine ⟨hf.1.comp_continuous (continuous_mul_const u), ?_⟩
  exact hf.2.comp_homeomorph (Homeomorph.mulRight u)

@[reducible] private def act {G : Type} [Group G] (B N : Subgroup G) : MulAction (B × N) G where
  smul h g := (h.1 : G) * g * (h.2 : G)⁻¹
  one_smul g := by
    show ((1 : B × N).1 : G) * g * ((1 : B × N).2 : G)⁻¹ = g
    simp
  mul_smul h k g := by
    show ((h * k).1 : G) * g * ((h * k).2 : G)⁻¹ =
      (h.1 : G) * ((k.1 : G) * g * (k.2 : G)⁻¹) * (h.2 : G)⁻¹
    simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, _root_.mul_inv_rev]
    group

private theorem orbit_act {G : Type} [Group G] (B N : Subgroup G) (w : G) :
    letI := act B N; orbit (B × N) w = cell B N w := by
  letI := act B N
  show orbit (B × N) w = cell B N w
  ext g
  constructor
  · rintro ⟨⟨b, u⟩, rfl⟩
    exact ⟨b, b.2, (u : G)⁻¹, N.inv_mem u.2, rfl⟩
  · rintro ⟨b, hb, u, hu, rfl⟩
    refine ⟨(⟨b, hb⟩, ⟨u, hu⟩⁻¹), ?_⟩
    show b * w * (((⟨u, hu⟩⁻¹ : N) : G))⁻¹ = b * w * u
    simp

theorem UpperTheory.Gal.LocD.biInv :
    DistInv → BiInv := by
  intro hD G _ _ _ _ _ _ _ B N hB hN s p hp hs hsp hsB hsN hC η θ hη hθ hηs hθs D hDB hDN f hf
  obtain ⟨L, hLo, hL⟩ := hη
  obtain ⟨k, w, hw1, hw2, hw3⟩ := hC
  letI := act B N
  haveI : LocallyCompactSpace B := hB.locallyCompactSpace
  haveI : LocallyCompactSpace N := hN.locallyCompactSpace
  haveI : SecondCountableTopology B := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SigmaCompactSpace (B × N) := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : ContinuousSMul (B × N) G := ⟨by
    show Continuous fun q : (B × N) × G => (q.1.1 : G) * q.2 * (q.1.2 : G)⁻¹
    exact ((continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).mul continuous_snd).mul
      (continuous_subtype_val.comp (continuous_snd.comp continuous_fst)).inv⟩
  let sB : B →* B := (s.comp B.subtype).codRestrict B (fun b => hsB b b.2)
  let sN : N →* N := (s.comp N.subtype).codRestrict N (fun u => hsN u u.2)
  let τ : B × N →* B × N := sB.prodMap sN
  have hτc : Continuous τ := by
    rw [MonoidHom.coe_prodMap]
    exact (Continuous.subtype_mk (hs.comp continuous_subtype_val) _).prodMap
      (Continuous.subtype_mk (hs.comp continuous_subtype_val) _)
  have hit : ∀ n (h : B × N), ((τ^[n] h).1 : G) = s^[n] h.1 ∧ ((τ^[n] h).2 : G) = s^[n] h.2 := by
    intro n
    induction n with
    | zero => intro h; simp
    | succ n ih =>
      intro h
      simp only [Function.iterate_succ_apply']
      exact ⟨by rw [← (ih h).1]; rfl, by rw [← (ih h).2]; rfl⟩
  let χ : B × N →* ℂ := (η.comp (MonoidHom.fst B N)) * ((Units.coeHom ℂ).comp (θ.comp (MonoidHom.snd B N)))
  have hχ : ∀ h : B × N, χ h = η h.1 * (θ h.2 : ℂ) := fun h => rfl
  refine hD G (B × N) s τ p hp hs hτc hsp ?_ ?_ χ ?_ ?_ k w hw1 ?_ ?_ D ?_ f hf
  · intro h
    have := hit p h
    exact Prod.ext (Subtype.ext (this.1.trans (hsp _))) (Subtype.ext (this.2.trans (hsp _)))
  · intro h x
    show s ((h.1 : G) * x * (h.2 : G)⁻¹) = s h.1 * s x * (s h.2)⁻¹
    simp [map_mul, map_inv]
  · refine ⟨(L.comap B.subtype).prod θ.ker, ?_, ?_⟩
    · rw [Subgroup.coe_prod]
      exact (hLo.preimage continuous_subtype_val).prod hθ
    · intro l hl
      rw [Subgroup.mem_prod] at hl
      rw [hχ, hL l.1 hl.1, MonoidHom.mem_ker.1 hl.2]
      simp
  · intro h
    rw [hχ, hχ, hηs h.1 (τ h).1 rfl, hθs h.2 (τ h).2 rfl]
  · intro y
    simpa only [orbit_act] using hw2 y
  · intro j
    simpa only [orbit_act] using hw3 j
  · intro h g hg
    have hg' : (fun x => g (x * (h.2 : G))) ∈ Cc G := mem_Cc_mul_right hg _
    have e : GroundTheory.Automorphic.Whittaker.transl h g = fun x => (fun y => g (y * (h.2 : G))) ((h.1 : G)⁻¹ * x) := by
      funext x
      show g (((h⁻¹).1 : G) * x * ((h⁻¹).2 : G)⁻¹) = g ((h.1 : G)⁻¹ * x * h.2)
      simp
    rw [e, hDB h.1 _ hg', hDN h.2 g hg, hχ, mul_assoc]
end

section

noncomputable section

open MeasureTheory

namespace UpperTheory.Gal.LocD

section Stable

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

private theorem mem_Cc {f : G → ℂ} : f ∈ Cc G ↔ IsLocallyConstant f ∧ HasCompactSupport f :=
  GroundTheory.Automorphic.mem_locallyConstantCompactSupport

private theorem Cc_comp_homeo {f : G → ℂ} (hf : f ∈ Cc G) (e : G ≃ₜ G) : f ∘ e ∈ Cc G := by
  rw [mem_Cc] at hf ⊢
  exact ⟨hf.1.comp_continuous e.continuous, hf.2.comp_homeomorph e⟩

private def homeoOf (s : G →* G) (p : ℕ) (hp : 0 < p) (hs : Continuous s) (hsp : ∀ g, s^[p] g = g) : G ≃ₜ G where
  toFun := s
  invFun := s^[p - 1]
  left_inv g := by
    have : s^[p - 1 + 1] g = g := by rw [Nat.sub_add_cancel hp]; exact hsp g
    rwa [Function.iterate_succ_apply] at this
  right_inv g := by
    have : s^[p - 1 + 1] g = g := by rw [Nat.sub_add_cancel hp]; exact hsp g
    rwa [Function.iterate_succ_apply'] at this
  continuous_toFun := hs
  continuous_invFun := hs.iterate _

end Stable

theorem funInv (hBi : BiInv) (hMem : PrMem) (hLeft : PrLeft) (hAuto : PrAuto) (hSurj : PrSurj) (hEta : EtaEx) :
    FunInv := by
  intro G _ _ _ _ _ _ _ B N hB hN K hKo hKc hBK s p hp hs hsp hsB hsN hC χ θ hχ hθ hχs hθs l hl φ hφ
  letI : MeasurableSpace B := borel B
  haveI : BorelSpace B := ⟨rfl⟩
  haveI : LocallyCompactSpace B := hB.locallyCompactSpace
  set μ : Measure B := Measure.haar with hμ
  obtain ⟨hmem, hadd⟩ := hMem G B hB μ χ hχ
  obtain ⟨f, hf, rfl⟩ := hSurj G B hB μ χ K hKo hKc hBK φ hφ
  by_cases hne : ∃ f ∈ Cc G, ∃ g, pr B μ χ f g ≠ 0
  swap
  · push_neg at hne
    have h0 : pr B μ χ f = 0 := funext (hne f hf)
    rw [h0]
    rfl
  obtain ⟨κ, hκ, hκs⟩ := hAuto G B hB μ χ s p hp hs hsp hsB hχs
  obtain ⟨hκ1, η, hη, hηL, hηs⟩ :=
    hEta G B s p hp hsp (pr B μ χ) κ hκ hκs (fun b => hLeft G B hB μ χ b) hne
  let prL : Cc G →ₗ[ℂ] (G → ℂ) :=
    { toFun := fun f => pr B μ χ f
      map_add' := fun f f' => hadd f f.2 f' f'.2
      map_smul' := fun c f => by
        funext g
        simp only [pr, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [← integral_const_mul]
        congr 1
        funext b
        ring }
  obtain ⟨q, hq⟩ := (Cc G).exists_isCompl
  let D : (G → ℂ) →ₗ[ℂ] ℂ := l ∘ₗ prL ∘ₗ (Cc G).projectionOnto q hq
  have hDf : ∀ f' (hf' : f' ∈ Cc G), D f' = l (pr B μ χ f') := by
    intro f' hf'
    show l (prL ((Cc G).projectionOnto q hq f')) = _
    rw [show (Cc G).projectionOnto q hq f' = ⟨f', hf'⟩ from
      Submodule.linearProjOfIsCompl_apply_left hq ⟨f', hf'⟩]
    rfl
  have hCs : f ∘ s ∈ Cc G := Cc_comp_homeo hf (homeoOf s p hp hs hsp)
  have hDleft : ∀ (b : B), ∀ f' ∈ Cc G, (D fun x => f' ((b : G)⁻¹ * x)) = η b * D f' := by
    intro b f' hf'
    have hmL : (fun x => f' ((b : G)⁻¹ * x)) ∈ Cc G :=
      Cc_comp_homeo hf' (Homeomorph.mulLeft ((b : G)⁻¹))
    have he : pr B μ χ (fun x => f' ((b : G)⁻¹ * x)) = η b • pr B μ χ f' :=
      funext fun g => hη b f' g
    rw [hDf _ hmL, hDf f' hf', he, map_smul, smul_eq_mul]
  have hDright : ∀ (u : N), ∀ f' ∈ Cc G, (D fun x => f' (x * (u : G))) = (θ u : ℂ) * D f' := by
    intro u f' hf'
    have hmR : (fun x => f' (x * (u : G))) ∈ Cc G :=
      Cc_comp_homeo hf' (Homeomorph.mulRight (u : G))
    have he : pr B μ χ (fun x => f' (x * (u : G))) = fun x => pr B μ χ f' (x * (u : G)) := by
      funext g
      simp only [pr, mul_assoc]
    rw [hDf _ hmR, hDf f' hf', he]
    exact hl u _ (hmem f' hf')
  have hps : pr B μ χ (f ∘ s) = pr B μ χ f ∘ s := by
    funext g
    rw [hκs, hκ1]
    simp
  rw [← hps, ← hDf _ hCs, ← hDf f hf]
  exact hBi G B N hB hN s p hp hs hsp hsB hsN hC η θ hηL hθ hηs hθs D hDleft hDright f hf

end UpperTheory.Gal.LocD

end
end
