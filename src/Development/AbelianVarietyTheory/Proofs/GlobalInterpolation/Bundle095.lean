module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle008
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle082
import Formalism.LocalToGlobal.Columns.BaseLemmas
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX.TieSame

theorem bsH_val_congr {e e' : Formalism.HC.Frame} (he : e = e') (h t : e.A) (h' t' : e'.A)
    (hh : h.val = h'.val) (ht : t.val = t'.val) : (Arith.bsH h t).val = (Arith.bsH h' t').val := by
  subst he
  have h1 := Formalism.HC.Frame.A.val_injective _ hh
  have h2 := Formalism.HC.Frame.A.val_injective _ ht
  rw [h1, h2]

theorem mem_iff_val_mem {e : Formalism.HC.Frame} (T : Finset e.A) (t : e.A) :
    t ∈ T ↔ t.val ∈ T.image Formalism.HC.Frame.A.val := by
  constructor
  · intro h; exact Finset.mem_image_of_mem _ h
  · intro h
    obtain ⟨s, hs, hst⟩ := Finset.mem_image.1 h
    rwa [← Formalism.HC.Frame.A.val_injective _ hst]

theorem kapISet_congr {D D' : D7} (L : SizeData₂ D) (L' : SizeData₂ D') (hR : D.R = D'.R) (hs : L.sc = L'.sc) (hS : L.Sc = L'.Sc)
    (K : G.Consts) (p n' : ℕ) (TT : Finset (Fin n')) (a b : Fin n' → ℤ) :
    G.kapISet L K p n' TT a b = G.kapISet L' K p n' TT a b := by
  have hk : D.R.k = D'.R.k := by rw [hR]
  have hc : G.cG L = G.cG L' := by unfold G.cG; rw [hS]
  have hD : G.DIf K L p n' = G.DIf K L' p n' := by unfold G.DIf; rw [hs, hk]
  have h6 : G.c6f K L p n' = G.c6f K L' p n' := by unfold G.c6f; rw [hD, hs, hk, hc]
  have ht : G.tIf K L p n' TT a b = G.tIf K L' p n' TT a b := by unfold G.tIf; rw [h6, hs, hk, hc]
  unfold G.kapISet
  rw [hc, hD, ht, hk]

theorem nonempty_place (D : D7) : Nonempty D.what₂.places.Pl := by
  haveI := D.nfLL
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 D.what₂.LL)
  exact ⟨D.plEq.symm ⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)⟩⟩

theorem off_lift {C : FC} {cD ch : ℝ} (p : Pt C) (hv : Val C cD ch p.L) (j : ℕ) (hj : j ∈ SizeData₂.lifts p.D) (t : G.HH p.D) :
    p.ta.Gx.off j (false, t) =
      (if t ∈ p.D.host.TT then ((⌊p.L.sc.b' / p.L.sc.x⌋ : ℤ) : ℝ) else ((⌈p.L.sc.w'' p.D.R.n⌉ : ℤ) : ℝ)) +
        ((j - 1 : ℕ) : ℝ) * (h0v p.L.sc ch : ℝ) + (h0v p.L.sc ch : ℝ) / 2 := by
  obtain ⟨w⟩ := nonempty_place p.D
  have hP := factPlaces p.D.R.toFrame
  have hmem : p.D.R.tau1 t ∈ p.D.R.Psi := (hP.1 _).2 (Or.inl ⟨t, rfl⟩)
  set τ := p.D.eTau.symm ⟨_, hmem⟩ with hτ
  have hτe : (p.D.eTau τ : p.D.R.GG) = p.D.R.tau1 t := by rw [hτ, Equiv.apply_symm_apply]
  have hf := (p.ta.fills w).1 j hj τ (false, t) (by rw [hτe]; rfl)
  have hjm : j - 1 < p.D.R.m := by
    have := Finset.mem_Icc.1 hj
    omega
  obtain ⟨-, -, ⟨b1, hb, htop, -, hthin⟩, -⟩ := hv.hc
  obtain ⟨hb1, hb2⟩ := hb τ ⟨j - 1, hjm⟩
  unfold wj at hf
  rw [dite_eq_left hjm, hb2, hb1] at hf
  unfold G.fill at hf
  by_cases ht : t ∈ p.D.host.TT
  · have h1 := htop τ ⟨t, ht⟩ hτe
    rw [if_pos ⟨rfl, ht⟩, h1] at hf
    rw [if_pos ht]
    unfold G.bL at hf
    rw [dite_eq_left ht] at hf
    push_cast at hf ⊢
    linarith
  · have h1 := hthin τ (by
      show p.D.host.IsThin (p.D.eTau τ : p.D.R.GG)
      rw [hτe]
      refine ⟨hmem, ?_, ?_⟩
      · intro h
        obtain ⟨s, hs, hst⟩ := Finset.mem_image.1 h
        have : s = t := p.D.R.iota_bijective.1 (congrArg Prod.snd hst)
        exact ht (this ▸ hs)
      · intro h
        obtain ⟨s, -, hst⟩ := Finset.mem_image.1 h
        exact hP.2 _ _ hst.symm)
    rw [if_neg (fun h => ht h.2), h1] at hf
    rw [if_neg ht]
    push_cast at hf ⊢
    linarith

theorem same_of_from : ∀ (C : FC) (cD ch : ℝ) (p p' : Pt C) (R : Ranks) (H : Host R) (a b : R.A → ℤ) (M : ℕ) (c : Fin M → Fin (R.k - 2) → Bool) (u0 u0' : ℕ), p.L.sc = p'.L.sc → Val C cD ch p.L → Val C cD ch p'.L → p.From H a b c u0 → p'.From H a b c u0' → CanonInst p.ta.Gx → CanonInst p'.ta.Gx → p.Same p' := by
  intro C cD ch p p' R H a b M c u0 u0' hs hv hv' hF hF' hC hC'
  have hQS := hF.QS_eq.trans hF'.QS_eq.symm
  have hart := hF.art_eq.trans hF'.art_eq.symm
  have hrd := hF.rd_eq.trans hF'.rd_eq.symm
  obtain ⟨hR, hTT, hT2, hq, hd, hg, hp1, hp2, -, -, hh, hw, -⟩ := hF
  obtain ⟨hR', hTT', hT2', hq', hd', hg', hp1', hp2', -, -, hh', hw', -⟩ := hF'
  have hRR : p.D.R = p'.D.R := hR.trans hR'.symm
  have hT : p.D.host.TT.image Formalism.HC.Frame.A.val = p'.D.host.TT.image Formalism.HC.Frame.A.val := hTT.trans hTT'.symm
  have hSc : p.L.Sc = p'.L.Sc := by rw [p.L.Sc_eq, p'.L.Sc_eq, hv.Del_eq, hv'.Del_eq, hs, hRR]
  have hmem : ∀ (t : G.HH p.D) (t' : G.HH p'.D), t.val = t'.val → (t ∈ p.D.host.TT ↔ t' ∈ p'.D.host.TT) := by
    intro t t' htt
    rw [mem_iff_val_mem p.D.host.TT t, mem_iff_val_mem p'.D.host.TT t', hT, htt]
  have hn : p.D.R.n = p'.D.R.n := by rw [hRR]
  refine ⟨hRR, hT, hT2.trans hT2'.symm, hq.trans hq'.symm, hd.trans hd'.symm, hg.trans hg'.symm, hp1.trans hp1'.symm,
    hp2.trans hp2'.symm, ?_, hSc, fun l => (hh l).trans (hh' l).symm, ?_, ?_, ?_, ?_, ?_, hQS, hart, hrd⟩
  · rw [hv.eta_eq, hv'.eta_eq, hs, hRR]
  · intro h t h' t' e1 e2
    rw [hC.1, hC'.1]
    exact bsH_val_congr (by rw [hRR]) h t h' t' e1 e2
  · intro j t t' htt
    have hm := hmem t t' htt
    have hl : SizeData₂.lifts p.D = SizeData₂.lifts p'.D := by unfold SizeData₂.lifts; rw [hRR]
    by_cases hj : j ∈ SizeData₂.lifts p.D
    · rw [off_lift p hv j hj t, off_lift p' hv' j (hl ▸ hj) t', hs, hn]
      by_cases ht : t ∈ p.D.host.TT
      · rw [if_pos ht, if_pos (hm.1 ht)]
      · rw [if_neg ht, if_neg (fun h => ht (hm.2 h))]
    · rw [hC.2 j hj t, hC'.2 j (hl ▸ hj) t', hs, hn]
      by_cases ht : t ∈ p.D.host.TT
      · rw [if_pos ht, if_pos (hm.1 ht)]
      · rw [if_neg ht, if_neg (fun h => ht (hm.2 h))]
  · funext l n' TT a' b'
    rw [p.xa.ex.kapI_def l n' TT a' b', p'.xa.ex.kapI_def l n' TT a' b', kapISet_congr p.L p'.L hRR hs hSc]
  · funext l
    rw [p.xa.ex.ep_def l, p'.xa.ex.ep_def l, hs, hRR]
  · intro t t' htt
    have hlt : (t : p.D.R.A).val < R.ord := by
      have := Formalism.HC.Frame.A.val_lt (t : p.D.R.A)
      rwa [show R.ord = p.D.R.ord by rw [hR]]
    have hv0 : (R.ofNat (t : p.D.R.A).val).val = (t : p.D.R.A).val :=
      R.toFrame.val_ofNat_of_lt hlt
    obtain ⟨e1, e2⟩ := hw t _ hv0.symm
    obtain ⟨e3, e4⟩ := hw' t' _ (htt.symm.trans hv0.symm)
    exact ⟨e1.trans e3.symm, e2.trans e4.symm⟩

end GlobalTheory.EX.TieSame
end

section

noncomputable section

namespace GlobalTheory.LvT.StabOrder

open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2

theorem rank_le (R : Ranks) {i j : ℕ} (h : i ≤ j) : R.N i ≤ R.N j := by
  unfold Ranks.N
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _

theorem prime_le_of_embed {E G : Type} [Field E] [NumberField E] [Group G] [Finite G] {n : ℕ}
    (φ : G →* ((Fin n → E) ≃ₗ[E] (Fin n → E))) (hφ : Function.Injective φ) {p : ℕ} (hp : p.Prime)
    (hd : p ∣ Nat.card G) : p ≤ Module.finrank ℚ E * n + 1 := by
  haveI : Finite φ.range := Finite.of_surjective _ φ.rangeRestrict_surjective
  have h := prime_le_of_dvd_card φ.range hp (by rwa [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv])
  rwa [Module.finrank_fin_fun] at h

theorem prime_le_of_embed_GL {E G : Type} [Field E] [NumberField E] [Group G] [Finite G] {n : ℕ}
    (φ : G →* GL (Fin n) E) (hφ : Function.Injective φ) {p : ℕ} (hp : p.Prime)
    (hd : p ∣ Nat.card G) : p ≤ Module.finrank ℚ E * n + 1 :=
  prime_le_of_embed ((LinearMap.GeneralLinearGroup.generalLinearEquiv E (Fin n → E)).toMonoidHom.comp
      ((Matrix.GeneralLinearGroup.toLin (n := Fin n) (R := E)).toMonoidHom.comp φ))
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv E (Fin n → E)).injective.comp
      ((Matrix.GeneralLinearGroup.toLin (n := Fin n) (R := E)).injective.comp hφ)) hp hd

section Concrete

variable {F : Fields} {Pr : Primes F} {R : Ranks} {W : Wts F Pr.Word R} {a : ℝ}

variable {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 F.E))}

variable (sel : HeightOneSpectrum (𝓞 F.F) → HeightOneSpectrum (𝓞 F.E)) {S : Set ℕ} (mu : Tup F.F F.E F.K S)
  (cst : LocCst F (rowSG Pr sel mu)) (L : ChIdx F Pr R (QE sel (mu : Chr F.F F.E F.K)))

end Concrete

section Record

variable {D : D7} {u : D.what₂.Word}

theorem stabUnit_of_embed (X : Ch D u) (E : Type) [Field E] [NumberField E]
    (hT : Module.finrank ℚ E * D.R.N D.R.m + 1 < X.A.T)
    (h : ∀ i, i ≤ D.R.m → ∀ c : X.C.cls i, ∃ j : X.C.stab i c →* GL (Fin (D.R.N i)) E, Function.Injective j) :
    StabUnit X := fun i hi c hd => by
  obtain ⟨j, hj⟩ := h i hi c
  have h1 := prime_le_of_embed_GL j hj X.A.T_prime hd
  have h2 := Nat.mul_le_mul_left (Module.finrank ℚ E) (rank_le D.R hi)
  omega

theorem stabUnit_of_chainIn (X : Ch D u) {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K]
    (I : ChainIn E K D.what₂.Tau D.R) (emb : D.what₂.Tau → E →+* K) (σ : K →+* ℂ) (hI : I.Ok)
    (hC : X.C = I.chain emb σ hI (D.hcW u)) (hT : Module.finrank ℚ E * D.R.N D.R.m + 1 < X.A.T) : StabUnit X := by
  refine stabUnit_of_embed X E hT ?_
  rw [hC]
  intro i _ c
  refine ⟨((I.S i).gam c.1).comp (MulAction.stabilizer _ ((I.S i).rep c)).subtype, ?_⟩
  rw [injective_iff_map_eq_one]
  exact fun g hg => Subtype.ext ((hI.step i).stab_inj c.1 g.1 _ g.2 hg)

end Record

end GlobalTheory.LvT.StabOrder
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory.MomT.IdxBound

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}

theorem mem_of_locP {W : Type} [AddCommGroup W] [Module (𝓞 E) W] (M : Submodule (𝓞 E) W) (x : W)
    (h : ∀ Q : HeightOneSpectrum (𝓞 E), x ∈ localization₂ Q.asIdeal M) : x ∈ M := by
  by_contra hx
  let I : Ideal (𝓞 E) := M.comap (LinearMap.toSpanSingleton (𝓞 E) W x)
  have hI : ∀ s, s ∈ I ↔ s • x ∈ M := fun s => Iff.rfl
  have hne : I ≠ ⊤ := fun e => hx (by simpa using (hI 1).1 (e ▸ Submodule.mem_top))
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal I hne
  have hm0 : m ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField E)
  obtain ⟨s, hs, hsx⟩ := (mem_locP ⟨m, hm.isPrime, hm0⟩ M x).1 (h _)
  exact hs (hle ((hI s).2 hsx))

theorem mem_localization_of_smul_mem {W : Type} [AddCommGroup W] [Module (𝓞 E) W] (P : HeightOneSpectrum (𝓞 E)) (M : Submodule (𝓞 E) W)
    {x : W} {s : 𝓞 E} (hs : s ∉ P.asIdeal) (h : s • x ∈ localization₂ P.asIdeal M) : x ∈ localization₂ P.asIdeal M := by
  obtain ⟨t, ht, htx⟩ := (mem_locP P M _).1 h
  refine (mem_locP P M _).2 ⟨t * s, fun h' => (P.isPrime.mem_or_mem h').elim ht hs, ?_⟩
  rwa [mul_smul]

theorem per_apply_mem {AA : Submodule (𝓞 E) E} {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)}
    {P : HeightOneSpectrum (𝓞 E)} (hA : localization₂ P.asIdeal AA = localization₂ P.asIdeal (1 : Submodule (𝓞 E) E))
    {y : HomE E a b} (hy : y ∈ perO AA N N') {v : Sp E a} (hv : v ∈ localization₂ P.asIdeal N) : y v ∈ localization₂ P.asIdeal N' := by
  obtain ⟨s', hs', hv'⟩ := (mem_locP P N v).1 hv
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨r, hr, x, hx, rfl⟩ := hz
    obtain ⟨s, hs, hr'⟩ := (mem_locP P _ r).1 (hA ▸ le_locP P AA hr)
    obtain ⟨t, ht⟩ := Submodule.mem_one.1 hr'
    refine mem_localization_of_smul_mem P _ hs (mem_localization_of_smul_mem P _ hs' (le_locP P _ ?_))
    have h1 : x (s' • v) ∈ N' := hx _ hv'
    have h2 : s' • s • (r • x) v = t • x (s' • v) := by
      rw [LinearMap.map_smul_of_tower, LinearMap.smul_apply, ← smul_assoc s r, ← ht, algebraMap_smul, smul_comm]
    rw [h2]
    exact N'.smul_mem t h1
  | zero => simp
  | add y z _ _ hy hz => simpa using add_mem hy hz
  | smul r z _ hz => simpa using Submodule.smul_mem _ r hz

theorem mem_localization_perO {AA : Submodule (𝓞 E) E} {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)}
    {P : HeightOneSpectrum (𝓞 E)} (hA : localization₂ P.asIdeal AA = localization₂ P.asIdeal (1 : Submodule (𝓞 E) E)) (hN : N.FG)
    {y : HomE E a b} (hy : ∀ v ∈ N, y v ∈ localization₂ P.asIdeal N') : y ∈ localization₂ P.asIdeal (perO AA N N') := by
  classical
  obtain ⟨S, rfl⟩ := hN
  choose! s hs hsy using fun v (hv : v ∈ S) => (mem_locP P N' _).1 (hy v (Submodule.subset_span hv))
  have hP : ∏ v ∈ S, s v ∉ P.asIdeal := fun h => by
    obtain ⟨v, hv, h'⟩ := (P.isPrime.prod_mem_iff).1 h
    exact hs v hv h'
  have hh : (∏ v ∈ S, s v) • y ∈ homO (Submodule.span (𝓞 E) (S : Set (Sp E a))) N' := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      rw [← Finset.prod_erase_mul S s hv, LinearMap.smul_apply, mul_smul]
      exact N'.smul_mem _ (hsy v hv)
    | zero => simp
    | add v w _ _ hv hw => rw [map_add]; exact add_mem hv hw
    | smul r v _ hv => rw [LinearMap.map_smul_of_tower]; exact N'.smul_mem r hv
  obtain ⟨t, ht, h1⟩ := (mem_locP P AA 1).1 (hA ▸ le_locP P _ (Submodule.one_le.1 le_rfl))
  refine mem_localization_of_smul_mem P _ hP (mem_localization_of_smul_mem P _ ht (le_locP P _ (Submodule.subset_span ⟨_, h1, _, hh, ?_⟩)))
  rw [smul_assoc t (1 : E), one_smul]

theorem smul_mem_per {AA : Submodule (𝓞 E) E} {N : Submodule (𝓞 E) (Sp E a)} {N' N'' : Submodule (𝓞 E) (Sp E b)}
    {w : 𝓞 E} (h : ∀ y ∈ N', (w : E) • y ∈ N'') {y : HomE E a b} (hy : y ∈ perO AA N N') : w • y ∈ perO AA N N'' := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨r, hr, x, hx, rfl⟩ := hz
    refine Submodule.subset_span ⟨r, hr, w • x, fun v hv => h _ (hx v hv), (smul_comm _ _ _).symm⟩
  | zero => simp
  | add y z _ _ hy hz => rw [smul_add]; exact add_mem hy hz
  | smul r z _ hz => rw [smul_comm]; exact Submodule.smul_mem _ r hz

theorem apply_mem_of_std {N' : Submodule (𝓞 E) (Sp E b)} {P : HeightOneSpectrum (𝓞 E)} {y : HomE E a b}
    (hy : ∀ i, y (Pi.single i 1) ∈ localization₂ P.asIdeal N') {v : Sp E a} (hv : v ∈ stdAt E a P) : y v ∈ localization₂ P.asIdeal N' := by
  obtain ⟨s, hs, hsv⟩ := (mem_locP P _ v).1 hv
  choose t ht using fun i => Submodule.mem_one.1 (Submodule.mem_pi.1 hsv i (Set.mem_univ _))
  refine mem_localization_of_smul_mem P _ hs ?_
  have e : s • v = ∑ i, t i • (Pi.single i 1 : Sp E a) := by
    ext j
    rw [← ht j]
    simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def]

  rw [← LinearMap.map_smul_of_tower, e, map_sum]
  exact Submodule.sum_mem _ fun i _ => by
    rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ _ (hy i)

theorem relIndex_per_dvd : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (SG : Finset (HeightOneSpectrum (𝓞 X.E))) (ϖ : 𝓞 X.E) (p : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (d : DecoSet (E := X.E) (n := b) (ST := divs ϖ) (SG := SG)) (N'' : Submodule (𝓞 X.E) (Sp X.E b)), A.AA.FG → A.AA ≠ ⊥ → A.AAUnit (divs ϖ) → ϖ ≠ 0 → (∀ P ∈ divs ϖ, Ideal.absNorm P.asIdeal = p) → IsSdLat N → IsSdLat N'' → (∀ P ∈ divs ϖ, localization₂ P.asIdeal N = stdAt X.E a P) → ((∀ y ∈ d.1.N, (ϖ : X.E) • y ∈ N'') ∧ (∀ y ∈ N'', star (ϖ : X.E) • y ∈ d.1.N) ∧ ∀ (P : ↥(divs ϖ)) (y : Sp X.E b), y ∈ localization₂ P.1.asIdeal N'' ↔ y ∈ d.1.at P.1 ∧ d.1.f P y = 0) → (per A N N'').toAddSubgroup.relIndex (per A N d.1.N).toAddSubgroup ∣ p ^ ((divs ϖ).card * a) := by
  intro X A a b SG ϖ p N d N'' _ _ hU h0 hp hN _ hstd ⟨h1, _, h3⟩
  have he : ∀ (P : ↥(divs ϖ)) (i : Fin a), (Pi.single i 1 : Sp X.E a) ∈ localization₂ P.1.asIdeal N := fun P i => by
    rw [hstd P.1 P.2]
    exact le_locP P.1 _ (by simpa using single_mem_stdLat (E := X.E) i 1)
  have hm : ∀ (x : (per A N d.1.N).toAddSubgroup) (P : ↥(divs ϖ)) (i : Fin a), x.1 (Pi.single i 1) ∈ d.1.at P.1 :=
    fun x P i => per_apply_mem (hU P.1 P.2) x.2 (he P i)
  let φ : (per A N d.1.N).toAddSubgroup →+ ((P : ↥(divs ϖ)) → Fin a → 𝓞 X.E ⧸ P.1.asIdeal) :=
    AddMonoidHom.mk' (fun x P i => d.1.f P (x.1 (Pi.single i 1))) fun x y => by
      funext P i
      exact d.2.f_add P _ (hm x P i) _ (hm y P i)
  have hker : φ.ker ≤ (per A N N'').toAddSubgroup.addSubgroupOf (per A N d.1.N).toAddSubgroup := by
    intro x hx
    refine mem_of_locP (per A N N'') x.1 fun Q => ?_
    by_cases hQ : Q ∈ divs ϖ
    · refine mem_localization_perO (hU Q hQ) hN.1.fg fun v hv => apply_mem_of_std (fun i => ?_) (hstd Q hQ ▸ le_locP Q N hv)
      exact (h3 ⟨Q, hQ⟩ _).2 ⟨hm x ⟨Q, hQ⟩ i, congrFun (congrFun hx ⟨Q, hQ⟩) i⟩
    · exact mem_localization_of_smul_mem Q _ (fun h => hQ ((mem_divs h0 Q).2 h)) (le_locP Q _ (smul_mem_per h1 x.2))
  have hc : Nat.card ((P : ↥(divs ϖ)) → Fin a → 𝓞 X.E ⧸ P.1.asIdeal) = p ^ ((divs ϖ).card * a) := by
    have : ∀ P : ↥(divs ϖ), Nat.card (Fin a → 𝓞 X.E ⧸ P.1.asIdeal) = p ^ a := fun P => by
      rw [Nat.card_fun, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, hp P.1 P.2]
      simp
    rw [Nat.card_pi, Finset.prod_congr rfl fun P _ => this P]
    simp [← pow_mul, mul_comm]
  refine (AddSubgroup.index_dvd_of_le hker).trans ?_
  rw [AddSubgroup.index_ker, ← hc]
  exact AddSubgroup.card_addSubgroup_dvd_card _

end GlobalTheory.MomT.IdxBound
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

noncomputable section

namespace GlobalTheory.MomT.Heis

theorem HV_conj {ι : Type} [Fintype ι] {a b : ℕ} (sc : ℝ) (x y : VV ι a b) :
    Formalism.L2.Ker.HV sc y x = (starRingEnd ℂ) (Formalism.L2.Ker.HV sc x y) := by

  simp only [Formalism.L2.Ker.HV, LinearMap.mk₂'ₛₗ_apply, map_mul, map_sum, Complex.conj_ofReal, Complex.conj_conj]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem alpha_opU_mul {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V)
    (hH : ∀ x y, H y x = (starRingEnd ℂ) (H x y)) (c : ℝ) (x y : V) (F : V → ℂ) (z : V) :
    alphaQ (c / 2) H x * opU H x (fun w => alphaQ (c / 2) H y * opU H y F w) z =
      Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (((c * (H x y).re + (H x y).im) / 2 : ℝ) : ℂ)) *
        (alphaQ (c / 2) H (x + y) * opU H (x + y) F z) := by
  simp only [alphaQ, opU, Formalism.L2.Th1.H.qOf]
  rw [← add_assoc z x y]
  have key : ∀ a b c d e f g u : ℂ, a + b + c + d = e + f + g →
      Complex.exp a * (Complex.exp b * (u * Complex.exp c) * Complex.exp d) =
        Complex.exp e * (Complex.exp f * (u * Complex.exp g)) := by
    intro a b c d e f g u h
    have : Complex.exp a * Complex.exp b * Complex.exp c * Complex.exp d =
        Complex.exp e * Complex.exp f * Complex.exp g := by
      simp only [← Complex.exp_add, h]
    linear_combination u * this
  apply key
  simp only [map_add (f := _), LinearMap.add_apply]
  rw [hH x y]
  have h1 : H x y = ((H x y).re : ℂ) + ((H x y).im : ℂ) * Complex.I := (Complex.re_add_im _).symm
  have h2 : (starRingEnd ℂ) (H x y) = ((H x y).re : ℂ) - ((H x y).im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  simp only [Complex.add_re, Complex.conj_re]
  rw [h2]
  generalize (H x y).re = r at *
  generalize (H x y).im = s at *
  rw [h1]
  push_cast
  ring

variable {X : Fields} (A : Amb X) {a b : ℕ}

theorem emb_add (x y : HomE X.E a b) : emb A (x + y) = emb A x + emb A y := map_add _ x y

theorem Wx_Wx (x y : HomE X.E a b) (F : VCx X.Tau a b → ℂ) :
    Wx A x (Wx A y F) = fun z => Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (coc A x y : ℂ)) * Wx A (x + y) F z := by
  funext z
  have := alpha_opU_mul (Formalism.L2.Ker.HV A.sc) (fun x y => HV_conj A.sc x y) (Real.sqrt A.d) (emb A x) (emb A y) F z
  rw [← emb_add] at this
  exact this

theorem imH_eq (x y : HomE X.E a b) : imH A x y = coc A x y - coc A y x := by
  simp only [coc, imH, altE]
  rw [HV_conj A.sc (emb A x) (emb A y)]
  simp only [Complex.conj_re, Complex.conj_im]
  ring

theorem imH_add_left (x y z : HomE X.E a b) : imH A (x + y) z = imH A x z + imH A y z := by
  simp only [imH, altE, emb_add, map_add (f := _), LinearMap.add_apply, Complex.add_im]

theorem imH_add_right (x y z : HomE X.E a b) : imH A x (y + z) = imH A x y + imH A x z := by
  simp only [imH, altE, emb_add, map_add (f := _), LinearMap.add_apply, Complex.add_im]

theorem Wx_comm (x y : HomE X.E a b) (F : VCx X.Tau a b → ℂ) :
    Wx A x (Wx A y F) = fun z => brkE A y x * Wx A y (Wx A x F) z := by
  rw [Wx_Wx, Wx_Wx, add_comm y x]
  funext z
  have : brkE A y x = Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (imH A x y : ℂ)) := rfl
  rw [this, ← mul_assoc, ← Complex.exp_add, imH_eq]
  congr 2
  push_cast
  ring

theorem contDiff_Wx (x : HomE X.E a b) (F : VCx X.Tau a b → ℂ) (k : ℕ) (hF : ContDiff ℂ k F) :
    ContDiff ℂ k (Wx A x F) := by
  have h : ContDiff ℂ k (fun z : VCx X.Tau a b => Formalism.L2.Ker.HV A.sc z (emb A x)) := by
    simp only [Formalism.L2.Ker.HV, LinearMap.mk₂'ₛₗ_apply]
    fun_prop
  unfold Wx opU
  exact contDiff_const.mul ((hF.comp (contDiff_id.add contDiff_const)).mul
    (((contDiff_const.mul h).sub contDiff_const).cexp))

theorem jetC_sum (κ : Type) (T : Finset κ) (c : κ → ℂ) (F : κ → VCx X.Tau a b → ℂ)
    (hF : ∀ i ∈ T, ∀ k : ℕ, ContDiff ℂ k (F i)) (m : DVar X.Tau a b →₀ ℕ) :
    jetC A.cD (fun z => ∑ i ∈ T, c i * F i z) m = ∑ i ∈ T, c i * jetC A.cD (F i) m := by
  classical
  have hd : ∀ n : ℕ, iteratedFDeriv ℂ n (fun z => ∑ i ∈ T, c i * F i z) 0 = ∑ i ∈ T, c i • iteratedFDeriv ℂ n (F i) 0 := by
    intro n
    have e : (fun z => ∑ i ∈ T, c i * F i z) = ∑ i ∈ T, c i • F i := by
      funext z; simp
    rw [e, iteratedFDeriv_sum_apply (f := fun i => c i • F i) (fun i hi => ((hF i hi n).const_smul (c i)).contDiffAt)]
    exact Finset.sum_congr rfl fun i hi => iteratedFDeriv_const_smul_apply (hF i hi n).contDiffAt
  simp only [jetC, derivAt0, hd, ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem calculus : ∀ (X : Fields) (A : Amb X) (a b : ℕ), (∀ (x y : HomE X.E a b) (F : VCx X.Tau a b → ℂ), Wx A x (Wx A y F) = fun z => Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (coc A x y : ℂ)) * Wx A (x + y) F z) ∧ (∀ (x y : HomE X.E a b) (F : VCx X.Tau a b → ℂ), Wx A x (Wx A y F) = fun z => brkE A y x * Wx A y (Wx A x F) z) ∧ (∀ x y : HomE X.E a b, imH A x y = coc A x y - coc A y x) ∧ (∀ x y z : HomE X.E a b, coc A (x + y) z = coc A x z + coc A y z ∧ coc A x (y + z) = coc A x y + coc A x z ∧ imH A (x + y) z = imH A x z + imH A y z ∧ imH A x (y + z) = imH A x y + imH A x z) ∧ (∀ y t : HomE X.E a b, brkE A y t = Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (imH A t y : ℂ))) ∧ (∀ y t : HomE X.E a b, brkE A y t = 1 ↔ ∃ n : ℤ, imH A t y = n) ∧ (∀ (x : HomE X.E a b) (F : VCx X.Tau a b → ℂ), (∀ k : ℕ, ContDiff ℂ k F) → ∀ k : ℕ, ContDiff ℂ k (Wx A x F)) ∧ (∀ (κ : Type) (T : Finset κ) (c : κ → ℂ) (F : κ → VCx X.Tau a b → ℂ), (∀ i ∈ T, ∀ k : ℕ, ContDiff ℂ k (F i)) → ∀ m, jetC A.cD (fun z => ∑ i ∈ T, c i * F i z) m = ∑ i ∈ T, c i * jetC A.cD (F i) m) := by
  intro X A a b
  refine ⟨Wx_Wx A, Wx_comm A, imH_eq A, fun x y z => ⟨?_, ?_, imH_add_left A x y z, imH_add_right A x y z⟩,
    fun _ _ => rfl, fun y t => ?_, fun x F hF k => contDiff_Wx A x F k (hF k), fun κ T c F hF m => jetC_sum A κ T c F hF m⟩
  · simp only [coc, imH_add_left, emb_add, map_add (f := _), LinearMap.add_apply, Complex.add_re]; ring
  · simp only [coc, imH_add_right, emb_add, map_add (f := _), LinearMap.add_apply, Complex.add_re]; ring
  · have : brkE A y t = Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (imH A t y : ℂ)) := rfl
    rw [this, Complex.exp_eq_one_iff]
    have hne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := Complex.two_pi_I_ne_zero
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨-n, ?_⟩
      have : ((imH A t y : ℝ) : ℂ) = ((-n : ℤ) : ℂ) := by
        apply mul_left_cancel₀ hne
        push_cast
        linear_combination -hn
      exact_mod_cast this
    · rintro ⟨n, hn⟩
      refine ⟨-n, ?_⟩
      rw [hn]
      push_cast
      ring

end GlobalTheory.MomT.Heis
end
end
