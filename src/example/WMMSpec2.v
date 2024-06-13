From sflib Require Import sflib.
From Paco Require Import paco.
From stdpp Require namespaces.
Require Import Coq.Classes.RelationClasses Lia Program.
From Fairness Require Export ITreeLib
     PCM IProp IPM WMM FairLock TicketLockW
     Mod Linking SCM Red Weakest FancyUpdate.
     From PromisingLib Require Import Loc Event.
     From PromisingSEQ Require Import Time View TView Cell Memory Local.

From Fairness Require Import NatStructs.
Section WSPEC.

Variable ident_src: ID.
Variable state_src: Type.

Variable gvars : list nat.

Variable funs : fname -> option (ktree (threadE void ()) Any.t Any.t) .

Definition tgt_mod funs : Mod.t :=
     {|
          Mod.state := ();
          Mod.ident := void;
          Mod.st_init := ();
          Mod.funs := funs;
     |}.

Definition tgt_mod' := tgt_mod funs.
Context `{Σ: GRA.t}.

Context `{Invs : @InvSet Σ}.

Context `{MONORA: @GRA.inG monoRA Σ}.
Context `{THDRA: @GRA.inG ThreadRA Σ}.
Context `{STATESRC: @GRA.inG (stateSrcRA (Mod.state (tgt_mod'))) Σ}.
Context `{STATETGT: @GRA.inG (stateTgtRA (OMod.closed_state tgt_mod' (WMem.mod))) Σ}.
Context `{IDENTSRC: @GRA.inG (identSrcRA (Mod.ident tgt_mod')) Σ}.
Context `{IDENTTGT: @GRA.inG (identTgtRA (OMod.closed_ident tgt_mod' (WMem.mod))) Σ}.

Context `{ARROWRA: @GRA.inG (ArrowRA (OMod.closed_ident tgt_mod' (WMem.mod))) Σ}.
(*
Context `{STATETGT: @GRA.inG (stateTgtRA ((OMod.closed_state ClientImpl.omod (ModAdd (WMem.mod) AbsLockW.mod)))) Σ}.
Context `{IDENTTGT: @GRA.inG (identTgtRA (OMod.closed_ident ClientImpl.omod (ModAdd (WMem.mod) AbsLockW.mod))%type) Σ}.
Context `{ARROWRA: @GRA.inG (ArrowRA (OMod.closed_ident ClientImpl.omod (ModAdd (WMem.mod) AbsLockW.mod))%type) Σ}.*)
Context `{OBLGRA: @GRA.inG ObligationRA.t Σ}.
Context `{EDGERA: @GRA.inG EdgeRA Σ}.
Context `{ONESHOTSRA: @GRA.inG (@FiniteMap.t (OneShot.t unit)) Σ}.

Context `{COPSETRA : @GRA.inG CoPset.t Σ}.
Context `{GSETRA : @GRA.inG Gset.t Σ}.
Context `{INVSETRA : @GRA.inG (InvSetRA Var) Σ}.

Context `{WMEMRA: @GRA.inG wmemRA Σ}.

Context `{EXCL: @GRA.inG (Excl.t unit) Σ}.
Context `{EXCL2: @GRA.inG (Excl.t (unit * unit)) Σ}.
Context `{ONESHOTRA: @GRA.inG (OneShot.t nat) Σ}.
Context `{REGIONRA: @GRA.inG (Region.t (thread_id * nat)) Σ}.
Context `{CONSENTRA: @GRA.inG (@FiniteMap.t (Consent.t nat)) Σ}.
Context `{AUTHNRA: @GRA.inG (Auth.t (Excl.t nat)) Σ}.
Context `{AUTHVWRA: @GRA.inG (Auth.t (Excl.t View.t)) Σ}.
Context `{AUTHVWRA2: @GRA.inG (Auth.t (Excl.t (View.t * unit))) Σ}.
Context `{AUTHNMNRA: @GRA.inG (Auth.t (NatMapRALarge.t nat)) Σ}.


Definition wP (n: nat): wProp := fun c _ => (exists m, (c = nat2c m) /\ (m < n)).
Definition wQ (n: nat): wProp := fun c _ => ((c = nat2c n)).

Lemma wload_fun_spec'''
l vw V k P Q 
tid E R_src R_tgt (Q' : R_src -> R_tgt -> iProp)
r g ps pt
itr_src ktr_tgt
st0 (mem: WMem.t)
:
(St_tgt (st0, mem))
-∗
(wpoints_to_full l V k (P) (Q))
-∗
(wmemory_black_strong mem)
-∗
(
∀vw'', ∀ v, ∀ j ,
St_tgt (st0, mem) -∗ 
(wpoints_to_full l V k P Q)
-∗
(
     ( FairRA.white (j) 1)
     ∗
     (lift_wProp P v vw'')
) 
     ∨ 
(   
     lift_wProp Q v vw'' 
     ∗
     (⌜View.le V vw'' ⌝)
)
-∗
(⌜View.le vw vw''⌝) -∗ (wmemory_black_strong mem)-∗ 
stsim tid E r g Q' ps true itr_src (ktr_tgt (vw'', v))
)
-∗
(stsim tid E r g Q' ps pt itr_src
(map_event (OMod.emb_callee tgt_mod' (WMem.mod)) (WMem.load_fun (vw, l, Ordering.acqrel)) >>= ktr_tgt))
.
iIntros "ST_TGT WPOINTS_TO_FULL WMEM  Q".
rred. iApply stsim_getR.
iSplit. iFrame.
rred.
iApply stsim_chooseR. iIntros "%".
destruct x. destruct x as [[lc1 val] to]. des. rename y into READ. rred.

iPoseProof (wmemory_ra_load_acq with "WMEM WPOINTS_TO_FULL") as "[%RVLE [MEM0 [MEM1 WCASES]]]".
eapply READ. eauto. auto. des.

iDestruct "WCASES" as "[[%WP [% [#WCOR %MISSED]]] | [%WQ %VVLE]]".

{ iApply stsim_fairR.
      { i. instantiate (1:=[]). exfalso. clear - IN. unfold prism_fmap, WMem.missed in IN. des_ifs. }
      { i. instantiate (1:=[inr (l, ts)]) in IN . inv IN. ss. inv H. }
      { econs. ii. inv H. econs. }
      { ss. }
      iIntros "_ WHITES".
      iDestruct "WHITES" as "[WHITE _]". clear MISSED.
      des.  rr in WP. des. rred.

      iPoseProof ("Q" with "[ST_TGT]") as "Q".
      iFrame.
      iPoseProof ("Q" with "[MEM1]") as "Q".
      iFrame.

      iPoseProof ("Q" with "[WHITE]") as "Q".
      iLeft. 
      iSplitL "WHITE". { iFrame. }
      eauto.
      iFrame.
      iPoseProof ("Q" with "[]") as "Q".
      {iPureIntro. eauto. }
      iPoseProof ("Q" with "[MEM0]") as "Q".
      iFrame.
      iFrame.
}

      iApply (stsim_fairR).
{  i. instantiate (1:= []). ss. clear - IN.
unfold prism_fmap, WMem.missed in IN. des_ifs.
}
{  i.  instantiate (1:=[]) in IN. inv IN. }
{ econs. }
{ auto. }
iIntros "_ _".
rred.
des.
iPoseProof ("Q" with "[ST_TGT]") as "Q".
iFrame.
iPoseProof ("Q" with "[MEM1]") as "Q".
iFrame.

iPoseProof ("Q" with "[]") as "Q".
iRight. eauto.
iPoseProof ("Q" with "[]") as "Q".
{iPureIntro. eauto. }
iPoseProof ("Q" with "[MEM0]") as "Q".
iFrame.
iFrame.
Unshelve.
eauto.
Qed.
     
      



Lemma wstore_fun_spec 
l vw V k P Q val
tid E R_src R_tgt (Q' : R_src -> R_tgt -> iProp)
r g ps pt
itr_src ktr_tgt
st0 (mem: WMem.t)
:
(St_tgt (st0, mem))
-∗
(wpoints_to_full l V k (P) (Q))
-∗
(wmemory_black_strong mem)
-∗
(
∀vw'', ∀ v, ∀ j ,
St_tgt (st0, mem) -∗ 
(wpoints_to_full l V k P Q)
-∗
(
     ( FairRA.white (j) 1)
     ∗
     (lift_wProp P v vw'')
) 
     ∨ 
(   
     lift_wProp Q v vw'' 
     ∗
     (⌜View.le V vw'' ⌝)
)
-∗
(⌜View.le vw vw''⌝) -∗ (wmemory_black_strong mem)-∗ 
stsim tid E r g Q' ps true itr_src (ktr_tgt (vw''))
)
-∗
(stsim tid E r g Q' ps pt itr_src
(map_event (OMod.emb_callee tgt_mod' (WMem.mod)) (WMem.store_fun (vw, l, val, Ordering.acqrel)) >>= ktr_tgt))
.
Abort.

Lemma wfaa_fun_spec : True.
Abort.



(*
(wmemory_black m)
-∗
(wpoints_to l v0 vw0)
-∗
((wmemory_black m) ∗ (⌜(View.le vw0 vw1) /\ (v0 = v1)⌝) ∗ #=>(wpoints_to l v0 vw1))
*)
End WSPEC.