module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle031
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle017
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle406
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle140
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle228
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityFamily
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle035
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle099
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle293
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideRationalCharacterData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle130
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle033
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle034
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData

@[expose] public section

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
noncomputable section
namespace GlobalTheory.SysFin
open GlobalTheory.CoefDuty
section Places
variable {R : Ranks} {H : Host R}
end Places
section Eig
variable {D : D7}
end Eig


open Classical in
theorem ptSys_finite_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ w : D.what₂.places.Pl, ∃ (F : Finset (PlE D.host)) (Sy : Finset (PlE D.host → ℕ → ℂ)), ∀ (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)) (Sp : NdSpec A.pl M C big L.X L.T), _root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tp.tup Sp.iq L.Y L.C → ∀ (i : (withLoc L).nd.Loc) (x : (withLoc L).nd.X i), (withLoc L).nd.w i = w → ∃ c ∈ Sy, ∀ v, v ∉ F → ∀ k, GlobalTheory.CoefDuty.ptSys (withLoc L) i x v k = c v k := by
  intro D cf jE A low Pq S hL eig θ Bs M C tp hCh hMt hstar hexp hsplit hcheb w
  by_cases hw0 : D.what₂.muAt w = D.what₂.mu0
  · refine ⟨∅, ∅, fun big L Sp Au i x hi => absurd hw0 ?_⟩
    have := L.X.w_tw i
    rw [show L.X.w i = w from hi] at this
    exact this
  choose nq hnq0 hnqm using fun q : PlE D.host => exists_intCast_mem q
  set N : ℤ := (D.host.g 0 : ℤ) * (D.host.g 1 : ℤ) * (D.host.pde : ℤ) * (D.host.pde' : ℤ) * ∏ q ∈ C.Q w, nq q with hNdef
  have hN : N ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_) ?_
    · exact_mod_cast (D.host.g_prime 0).ne_zero
    · exact_mod_cast (D.host.g_prime 1).ne_zero
    · exact_mod_cast D.host.pde_prime.ne_zero
    · exact_mod_cast D.host.pde'_prime.ne_zero
    · exact Finset.prod_ne_zero_iff.2 fun q _ => hnq0 q
  have hfinN := finite_intCast_mem (K := D.host.E) N hN
  set F : Finset (PlE D.host) := hfinN.toFinset with hFdef
  have hF : ∀ v : PlE D.host, v ∉ F → (N : 𝓞 D.host.E) ∉ v.asIdeal := fun v hv h => hv (hfinN.mem_toFinset.2 h)
  set l := D.what₂.places.resChar w with hldef
  set Q' : Finset (PlE D.host) := C.Q w ∪ F with hQ'
  have hB : ∀ (j : Fin D.R.m) v k (s : SplitPlace D.host.E), GenAt D l Q' v k → IsConjPl D.host v s.w →
      s.v ∉ gPl D ∪ qPl D (tp.tup (D.what₂.muTw w) j) := by
    intro j v k s hg hc hs
    have hvF : v ∉ F := fun h => hg.2.2.2.1 (Finset.mem_union_right _ h)
    have key : ∀ (w' : PlE D.host) (n : ℤ), NG.OverPl w' s.v → n ∣ N → (n : 𝓞 D.host.E) ∉ w'.asIdeal := by
      intro w' n hov hd hn
      apply hF v hvF
      apply intCast_mem_of_dvd hd
      rw [intCast_mem_conj hc, intCast_mem_over s.w_under]
      exact (intCast_mem_over hov n).1 hn
    rcases hs with ⟨w', hov, k0, hk0⟩ | hq
    · refine key w' (D.host.g k0) hov ?_ (by exact_mod_cast hk0)
      fin_cases k0
      · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) _) _
      · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) _) _
    · obtain ⟨w', hov, hw'⟩ := GlobalTheory.FitHecke.qPl_sub tp w hw0 j hq
      rcases hw' with hQ | hp
      · exact key w' (nq w') hov (Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ hQ) _) (hnqm w')
      · split_ifs at hp
        · exact key w' D.host.pde' hov (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) (by exact_mod_cast hp)
        · exact key w' D.host.pde hov (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) _) (by exact_mod_cast hp)
  have hfin : ∀ j : Fin D.R.m, (EigSet (M (D.what₂.muTw w) (j.1 + 1) (by omega) (by omega)) l Q').Finite := fun j =>
    GlobalTheory.T.heckeEigenvalueSystemSet_finite GlobalTheory.T.heckeDoubleCosetOperators_standardFacts D _ _ _ l Q' _ (hMt.hyp w j) (hB j)
  refine ⟨F, Finset.univ.biUnion fun j : Fin D.R.m => (hfin j).toFinset, fun big L Sp Au i x hi => ?_⟩
  obtain ⟨Hk, -⟩ := _root_.GlobalTheory.FitHecke.heckeOpen_withLoc_alt D cf jE A low Pq S hL eig θ Bs M C tp hCh hMt hstar hexp hsplit hcheb big L Sp Au
  have hpt := GlobalTheory.T.localisationPointEigenSystem_mem (withLoc L) (mtL L M) Hk.av i x
  have hwi : L.X.w i = w := hi
  have hl : L.X.l i = l := by rw [← L.X.w_l i, hwi]
  have hmem := GlobalTheory.FitHecke.mem_locs_self (D := withLoc L) i
  have hQ : L.X.Q i = C.Q w := by rw [← hwi]; exact (Sp.Q_eq _ _ i hmem).trans (Sp.Qc_eq _ _)
  have hj := L.X.j_range i
  let jf : Fin D.R.m := ⟨L.X.j i - 1, by omega⟩
  have hpt' : ptSys (withLoc L) i x ∈ EigSet (M (L.X.mu i) (L.X.j i) hj.1 hj.2) l (C.Q w) := by
    rw [← hl, ← hQ]; exact hpt
  have hpt'' := eigSet_transport M ((L.X.mu_w i).trans (by rw [hwi])) (show L.X.j i = jf.1 + 1 by simp [jf]; omega)
    hj.1 hj.2 (by omega) (by omega) l (C.Q w) _ hpt'
  refine ⟨fun v k => if GenAt D l Q' v k then ptSys (withLoc L) i x v k else 0, ?_, ?_⟩
  · refine Finset.mem_biUnion.2 ⟨jf, Finset.mem_univ _, (hfin jf).mem_toFinset.2 ?_⟩
    exact eigSet_restrict _ l Finset.subset_union_left hpt''
  · intro v hv k
    show _ = if GenAt D l Q' v k then _ else _
    split_ifs with hg
    · rfl
    · unfold ptSys
      rw [if_neg]
      intro hg'
      apply hg
      have hg2 : GenAt D l (C.Q w) v k := by rw [← hl, ← hQ]; exact hg'
      exact ⟨hg2.1, hg2.2.1, hg2.2.2.1, fun h => (Finset.mem_union.1 h).elim hg2.2.2.2.1 hv, hg2.2.2.2.2⟩
end GlobalTheory.SysFin
end
end
end

section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal
namespace GlobalTheory.ChiTame
section General
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
end General
theorem chi_one_tameGen_alt : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T), ∀ (Y : LocAut X) (Cb : LocBC Y), _root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tp.tup Sp.iq Y Cb → ∀ (i : X.nd.Loc) k v, X.nd.l i ≠ D.host.g k → haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; ∃ u : (ZMod (D.host.g k))ˣ, (u = D.nd.chiT k v ⟨X.nd.j i - 1, by have := X.nd.j_range i; omega⟩ ∨ u = (D.nd.chiT k v ⟨X.nd.j i - 1, by have := X.nd.j_range i; omega⟩)⁻¹) ∧ iotaO X.nd Y.naut i ((X.nd.chi i 1 (D.ntypes.tg k v) : (X.nd.O i)ˣ) : X.nd.O i) = D.ntypes.teichC k (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) (u : ZMod (D.host.g k))) := by
  intro hP D cf jE A low Pq S hL eig θ Bs M C tp h1 h2 h3 he h5 h6 big X T Sp Y Cb hAu i k v hl
  obtain ⟨art, ha⟩ := hP D.host.E D.nd.Om
  have hj := X.nd.j_range i
  let j' : Fin D.R.m := ⟨X.nd.j i - 1, by omega⟩
  obtain ⟨n, hG⟩ := _root_.GlobalTheory.ChiLocGal.chi1_loc_isGal_alt D cf jE A low Pq S hL eig θ Bs M C tp h1 h2 h3 he h5 h6 big X T Sp Y Cb
    hAu art ha i j' (by simp only [j']; omega)
  let C' : GlobalTheory.Mem.Chr.HFrame D.host (eExp D) :=
    ⟨cf.P, cf.W, cf.mu0, cf.eta, cf.chiPsi, cf.del, cf.del', cf.isMu0, cf.isEta, cf.isChi, cf.isDel, cf.isDel'⟩
  have hlp : (X.nd.l i).Prime := Fact.out
  have hgp := D.host.g_prime k
  have hwg : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw k v).asIdeal := D.naut.plGw_over k v
  obtain ⟨hN, hg2, -⟩ := GlobalTheory.Mem.Chr.splitsC_main D.R D.host _ hgp (D.nd.g_split k) _ hwg
  have hwl : ((X.nd.l i : ℕ) : 𝓞 D.host.E) ∉ (D.naut.plGw k v).asIdeal :=
    GlobalTheory.GalChar.notMem_of_ne hgp hlp hl.symm hwg
  have hA := D.nd.plOm.2 (D.naut.plGw k v)
  obtain ⟨hp, -, hpg, -, hD⟩ := GlobalTheory.GalChar.inertialOrderFifteenChar_auxiliaryPrime_spec C' (l := X.nd.l i)
  have hdel : (cf.delAt (X.nd.l i)).UnrAt (D.naut.plGw k v) :=
    hD.unr _ (GlobalTheory.GalChar.notMem_of_ne hgp hp (hpg k).symm hwg)
  have hloc : ∀ x, IsUnitAt (D.naut.plGw k v) x →
      (GlobalTheory.GalChar.block (cf.mu0 j' * cf.delAt (X.nd.l i)) cf.eta D.R.r).loc (D.naut.plGw k v) x =
        (cf.mu0 j').loc (D.naut.plGw k v) x := fun x hx => by
    rw [GlobalTheory.GalChar.block_loc (cf.isEta.unr _) hx]
    change (cf.mu0 j').loc _ x * (cf.delAt (X.nd.l i)).loc _ x = _
    rw [hdel x hx, mul_one]
  have hI := (hG.ine_pow_iff ha (Or.inl hwl) hA (D.host.g k - 1)).2 fun x hx => by
    rw [hloc x hx, ← hN]
    exact (GlobalTheory.Mem.WildChar.orders_on_units _ _ _).1 ((cf.isMu0 j').tame _) x hx
  haveI := D.host.isCMField_hostE
  obtain ⟨u, hu, hrep, hunit, σ, eσ, hσ⟩ := exists_tameRep hP ha hA hgp
    ((GlobalTheory.ChiLocGal.normV_eq_absNorm _).trans hN) hwg hg2 (fun a ha' x hx => isUnitAt_nat hwg ha' hx)
    (D.ntypes.tg_gen k v) _ (hG.cont (X.nd.O_adic i) (Sp.iq_alg i)) fun σ hσ => by
      rw [← map_pow, GlobalTheory.GalChar.inQ_eq_one, map_pow, hI σ hσ]
  obtain ⟨c, hc, hcv⟩ := A.chiT k v j' u hu hrep
  refine ⟨c, hc, ?_⟩
  have hvS : D.naut.plGw k v ∈ X.nd.S i := by
    rw [X.nd.S_def i]
    refine ⟨?_, hwl⟩
    fin_cases k
    · exact Or.inl hwg
    · exact Or.inr (Or.inl hwg)
  have hvQ : D.naut.plGw k v ∉ X.nd.Q i := fun h => (Finset.disjoint_left.mp (X.nd.SQ_disj i) hvS) h
  have hψ : T.psiL i (D.ntypes.tg k v) = 1 := by
    by_contra hne
    exact hvQ ((T.psiL_ram i _ _ hA).mp ⟨_, D.ntypes.tg_mem k v, hne⟩)
  have e1 := hG.loc (Or.inl hwl) eσ
  rw [GlobalTheory.GalChar.inQ_inj _ hσ, hloc _ hunit] at e1
  have e2 : X.nd.chi i 1 (D.ntypes.tg k v) = ((Units.map (T.twist₂ i).toMonoidHom).comp
      (D.ntw.chi1 (T.twOf i) (X.nd.j i) (T.twSide i))) (D.ntypes.tg k v) := by
    refine (DFunLike.congr_fun (T.chi_tw i) _).trans ?_
    exact (congrArg (_ * ·) hψ).trans (mul_one _)
  rw [← hcv, e2]
  refine Eq.trans ?_ e1
  unfold iotaO
  rw [hAu.iotaQ i]
  rfl
end GlobalTheory.ChiTame
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.galois_family_residual_image_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (hψ : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → (tp.psi w).ValuesIn 0 D.what₂.embLL) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc) (j : Fin D.R.m), j.1 + 1 = X.nd.j i → ∃ Bf : Finset (HeightOneSpectrum (𝓞 D.host.E)), ∀ P ∉ Bf, (tp.tup (X.nd.mu i) j * cf.eta⁻¹).UnrAt P ∧ ∀ σ : Formalism.ConjugateSelfDual.G D.host.E X.nd.Om, IsFrob (F := D.host.E) (X.nd.plOm.1 P) (normV P) σ → (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) (Sp.iq i (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)) ((X.nd.chi i 1 σ : (X.nd.O i)ˣ) : X.nd.O i))) = (((tp.tup (X.nd.mu i) j * cf.eta⁻¹).val P)⁻¹ : ℂˣ).1 * ((normV P : ℕ) : ℂ) ^ (((((D.R.t : ℝ) - 1) / 2 + (1 - (D.R.nV : ℝ)) / 2) : ℝ) : ℂ) := by
  first | exact @_root_.GlobalTheory.ChiOneRead.chiOne_read_alt | exact _root_.GlobalTheory.ChiOneRead.chiOne_read_alt | (intros; apply _root_.GlobalTheory.ChiOneRead.chiOne_read_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.exists_galois_rep_of_cuspidal_alt : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE), GalEx D → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (π : D.naut.CG D.R.r), D.naut.csd π → D.naut.ralg π → ∃ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.r) (Qbar l), IsRepOf D l ι (D.naut.tw π D.naut.etaTinv) ((1 - (D.R.nV : ℝ)) / 2) ρ := by
  first | exact @_root_.GlobalTheory.HeightCounting.TwistAny.exists_isRepOf_tw_alt | exact _root_.GlobalTheory.HeightCounting.TwistAny.exists_isRepOf_tw_alt | (intros; apply _root_.GlobalTheory.HeightCounting.TwistAny.exists_isRepOf_tw_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.galois_family_crystalline_weights_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc), ∃ μ : D.naut.CG 1, D.naut.csd μ ∧ ∀ j : Fin D.R.m, j.1 + 1 = X.nd.j i → (A.chr.e1 μ).1 = tp.tup (X.nd.mu i) j := by
  first | exact @_root_.GlobalTheory.MuCLoc.exists_muC_alt | exact _root_.GlobalTheory.MuCLoc.exists_muC_alt | (intros; apply _root_.GlobalTheory.MuCLoc.exists_muC_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.galois_family_irreducible_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc) (ι : Type) [Finite ι] (F : ι → Submodule ℂ (GAf D.host.E D.R.nV → (mlX M X i).wt.W)) (irr : ∀ P, NG.IsIrrRep (mlX M X i).wt.ρ (F P)) (hinj : ∀ P P', NG.IsoRep (F P) (F P') → P = P') (hsurj : ∀ S', NG.IsIrrRep (mlX M X i).wt.ρ S' → (NG.isoTyp (mlX M X i).wt.ρ S').comap (mlX M X i).real ≠ ⊥ → ∃ P, NG.IsoRep (F P) S') (hne : ∀ P, (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real ≠ ⊥) (hind : iSupIndep (fun P => (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real)) (htop : ⨆ P, (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real = ⊤) (P : ι) (w : PlE D.host), IsSplitPl D.host w → w ∉ X.nd.Q i → (∀ k, w ∉ placesOver D.host.E (D.host.g k)) → w ∉ placesOver D.host.E (if X.nd.l i = D.host.pde then D.host.pde' else D.host.pde) → D.naut.unr (D.nbc.locAU (X.nd.j i) (A.au.cls (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2 { (mlX M X i).wt with S := F P, irrS := irr P }) w) := by
  first | exact @_root_.GlobalTheory.AutUnr.locV_unr_m_alt | exact _root_.GlobalTheory.AutUnr.locV_unr_m_alt | (intros; apply _root_.GlobalTheory.AutUnr.locV_unr_m_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.infG_eq_half_integer : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (t : D.what₂.Tau) (sh : ℂ),
    D.naut.infG D.naut.etaT (embT D t) = {sh} → ∃ z : ℤ, sh = (z : ℂ) + 1 / 2 := by
  first | exact @_root_.GlobalTheory.EtaTildeShift.sh_half_alt | exact _root_.GlobalTheory.EtaTildeShift.sh_half_alt | (intros; apply _root_.GlobalTheory.EtaTildeShift.sh_half_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.galois_family_unramified_outside_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc) (ι : Type) [Finite ι] (F : ι → Submodule ℂ (GAf D.host.E D.R.nV → (mlX M X i).wt.W)) (irr : ∀ P, NG.IsIrrRep (mlX M X i).wt.ρ (F P)) (hinj : ∀ P P', NG.IsoRep (F P) (F P') → P = P') (hsurj : ∀ S', NG.IsIrrRep (mlX M X i).wt.ρ S' → (NG.isoTyp (mlX M X i).wt.ρ S').comap (mlX M X i).real ≠ ⊥ → ∃ P, NG.IsoRep (F P) S') (hne : ∀ P, (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real ≠ ⊥) (hind : iSupIndep (fun P => (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real)) (htop : ⨆ P, (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real = ⊤) (ptV : ι → Option (X.nd.X i)), (∀ P x, ptV P = some x ↔ (∀ (w : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), SplitOut X.nd i w → IsConjPl D.host w s.w → IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∀ y ∈ ((NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real), NG.tN (mlX M X i).J s ϖ k ((mlX M X i).real y) = (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) ((X.nd.hT i w k : X.nd.X i → X.nd.O i) x) • (mlX M X i).real y)) → (∀ x, ∃ P, ptV P = some x) ∧ ∀ x, X.nd.mult i x = Module.finrank ℂ ↥(⨆ P ∈ {P | ptV P = some x}, ((NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real)) := by
  first | exact @_root_.GlobalTheory.AutPts.automorphic_points_exist | exact _root_.GlobalTheory.AutPts.automorphic_points_exist | (intros; apply _root_.GlobalTheory.AutPts.automorphic_points_exist <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.galois_family_places_over_real_alt : ∀ (hArt : GlobalTheory.Published.GlobalArtinReciprocity) (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc) (j : Fin D.R.m), j.1 + 1 = X.nd.j i → (∃ Bf : Finset (HeightOneSpectrum (𝓞 D.host.E)), ∀ P ∉ Bf, (tp.tup (X.nd.mu i) j * cf.eta⁻¹).UnrAt P ∧ ∀ σ : Formalism.ConjugateSelfDual.G D.host.E X.nd.Om, IsFrob (F := D.host.E) (X.nd.plOm.1 P) (normV P) σ → (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) (Sp.iq i (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)) ((X.nd.chi i 1 σ : (X.nd.O i)ˣ) : X.nd.O i))) = (((tp.tup (X.nd.mu i) j * cf.eta⁻¹).val P)⁻¹ : ℂˣ).1 * ((normV P : ℕ) : ℂ) ^ (((((D.R.t : ℝ) - 1) / 2 + (1 - (D.R.nV : ℝ)) / 2) : ℝ) : ℂ)) → ∀ w, SplitOut X.nd i w → ∀ (B : ValuationSubring X.nd.Om) (σ : Formalism.ConjugateSelfDual.G D.host.E X.nd.Om), IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) σ → (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) (Sp.iq i (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)) ((X.nd.chi i 1 σ : (X.nd.O i)ˣ) : X.nd.O i))) = (((tp.tup (X.nd.mu i) j * cf.eta⁻¹).val w)⁻¹ : ℂˣ).1 * ((normV w : ℕ) : ℂ) ^ (((((D.R.t : ℝ) - 1) / 2 + (1 - (D.R.nV : ℝ)) / 2) : ℝ) : ℂ) := by
  first | exact @_root_.GlobalTheory.ChiMuArtin.chiMu_frob_all_alt | exact _root_.GlobalTheory.ChiMuArtin.chiMu_frob_all_alt | (intros; apply _root_.GlobalTheory.ChiMuArtin.chiMu_frob_all_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.galois_family_local_condition_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc) (V : Submodule ℂ (D.what₂.Mt (X.nd.mu i) (X.nd.j i))), V ≠ ⊥ → ∀ x x' : X.nd.X i, (∀ (w : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), SplitOut X.nd i w → IsConjPl D.host w s.w → IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∀ y ∈ V, NG.tN (mlX M X i).J s ϖ k ((mlX M X i).real y) = (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) ((X.nd.hT i w k : X.nd.X i → X.nd.O i) x) • (mlX M X i).real y) → (∀ (w : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), SplitOut X.nd i w → IsConjPl D.host w s.w → IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∀ y ∈ V, NG.tN (mlX M X i).J s ϖ k ((mlX M X i).real y) = (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) ((X.nd.hT i w k : X.nd.X i → X.nd.O i) x') • (mlX M X i).real y) → x = x' := by
  first | exact @_root_.GlobalTheory.HeckePointUniq.eq_of_eigen_alt | exact _root_.GlobalTheory.HeckePointUniq.eq_of_eigen_alt | (intros; apply _root_.GlobalTheory.HeckePointUniq.eq_of_eigen_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.galois_family_determinant_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc), ∃ κ : IsLocalRing.ResidueField (X.nd.O i) →+* Formalism.CyclotomicNorms.Fbar (X.nd.l i), ∀ y : X.nd.O i, ∃ h : (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) y ∈ A.pl.plB (X.nd.w i), fbCast (X.nd.w_l i) (D.what₂.places.resChar_prime (X.nd.w i)) (X.nd.lPrime i).out (A.pl.plκ (X.nd.w i) (IsLocalRing.residue (A.pl.plB (X.nd.w i)) ⟨_, h⟩)) = κ (IsLocalRing.residue (X.nd.O i) y) := by
  first | exact @_root_.GlobalTheory.ResidueLocPlace.exists_residueField_map_alt | exact _root_.GlobalTheory.ResidueLocPlace.exists_residueField_map_alt | (intros; apply _root_.GlobalTheory.ResidueLocPlace.exists_residueField_map_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.side_multiplicity_character_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)) (Sp : NdSpec A.pl M C big L.X L.T) (Au : _root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tp.tup Sp.iq L.Y L.C), Nonempty (TwOpen (withLoc L) (chL L C) (cfL L cf) (tpL L tp) (mtL L M) low) := by
  first | exact @_root_.GlobalTheory.HeightCounting.FitTw.nonempty_twOpen_alt | exact _root_.GlobalTheory.HeightCounting.FitTw.nonempty_twOpen_alt | (intros; apply _root_.GlobalTheory.HeightCounting.FitTw.nonempty_twOpen_alt <;> assumption)
end
end
