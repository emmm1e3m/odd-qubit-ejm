import UnifiedEJM.PhysicsClosureNodes
import UnifiedEJM.PhysicsClosureTerminal

open OddEJM
open scoped BigOperators
namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
open UnifiedEJM.PathCutScore
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open UnifiedEJM.PhysicsEntanglement

theorem nodeIntegerBound0512 : ∀ pen last, terminalScore 512 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 512).parity (tailData 512 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 512 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0934
  · exact terminalBound0935
  · exact terminalBound0944
  · exact terminalBound0945
theorem nodeIntegerBound0513 : ∀ pen last, terminalScore 513 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 513).parity (tailData 513 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 513 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0946
  · exact terminalBound0947
  · exact terminalBound0948
  · exact terminalBound0949
theorem nodeIntegerBound0514 : ∀ pen last, terminalScore 514 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 514).parity (tailData 514 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 514 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0926
  · exact terminalBound0927
  · exact terminalBound0950
  · exact terminalBound0951
theorem nodeIntegerBound0515 : ∀ pen last, terminalScore 515 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 515).parity (tailData 515 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 515 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0944
  · exact terminalBound0945
  · exact terminalBound0936
  · exact terminalBound0937
theorem nodeIntegerBound0516 : ∀ pen last, terminalScore 516 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 516).parity (tailData 516 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 516 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0952
  · exact terminalBound0953
  · exact terminalBound0948
  · exact terminalBound0949
theorem nodeIntegerBound0517 : ∀ pen last, terminalScore 517 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 517).parity (tailData 517 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 517 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0942
  · exact terminalBound0943
  · exact terminalBound0404
  · exact terminalBound0405
theorem nodeIntegerBound0518 : ∀ pen last, terminalScore 518 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 518).parity (tailData 518 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 518 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0938
  · exact terminalBound0939
  · exact terminalBound0954
  · exact terminalBound0955
theorem nodeIntegerBound0519 : ∀ pen last, terminalScore 519 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 519).parity (tailData 519 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 519 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0956
  · exact terminalBound0957
  · exact terminalBound0948
  · exact terminalBound0949
theorem nodeIntegerBound0520 : ∀ pen last, terminalScore 520 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 520).parity (tailData 520 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 520 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0946
  · exact terminalBound0947
  · exact terminalBound0948
  · exact terminalBound0949
theorem nodeIntegerBound0521 : ∀ pen last, terminalScore 521 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 521).parity (tailData 521 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 521 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0958
  · exact terminalBound0959
  · exact terminalBound0948
  · exact terminalBound0949
theorem nodeIntegerBound0522 : ∀ pen last, terminalScore 522 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 522).parity (tailData 522 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 522 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0924
  · exact terminalBound0925
  · exact terminalBound0960
  · exact terminalBound0961
theorem nodeIntegerBound0523 : ∀ pen last, terminalScore 523 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 523).parity (tailData 523 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 523 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0942
  · exact terminalBound0943
  · exact terminalBound0404
  · exact terminalBound0405
theorem nodeIntegerBound0524 : ∀ pen last, terminalScore 524 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 524).parity (tailData 524 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 524 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0962
  · exact terminalBound0939
  · exact terminalBound0963
  · exact terminalBound0964
theorem nodeIntegerBound0525 : ∀ pen last, terminalScore 525 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 525).parity (tailData 525 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 525 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0926
  · exact terminalBound0927
  · exact terminalBound0965
  · exact terminalBound0951
theorem nodeIntegerBound0526 : ∀ pen last, terminalScore 526 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 526).parity (tailData 526 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 526 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0966
  · exact terminalBound0957
  · exact terminalBound0967
  · exact terminalBound0949
theorem nodeIntegerBound0527 : ∀ pen last, terminalScore 527 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 527).parity (tailData 527 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 527 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0926
  · exact terminalBound0927
  · exact terminalBound0968
  · exact terminalBound0969
theorem nodeIntegerBound0528 : ∀ pen last, terminalScore 528 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 528).parity (tailData 528 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 528 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0970
  · exact terminalBound0955
  · exact terminalBound0963
  · exact terminalBound0964
theorem nodeIntegerBound0529 : ∀ pen last, terminalScore 529 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 529).parity (tailData 529 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 529 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0971
  · exact terminalBound0959
  · exact terminalBound0967
  · exact terminalBound0949
theorem nodeIntegerBound0530 : ∀ pen last, terminalScore 530 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 530).parity (tailData 530 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 530 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0972
  · exact terminalBound0943
  · exact terminalBound0417
  · exact terminalBound0405
theorem nodeIntegerBound0531 : ∀ pen last, terminalScore 531 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 531).parity (tailData 531 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 531 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0807
  · exact terminalBound0973
  · exact terminalBound0974
  · exact terminalBound0937
theorem nodeIntegerBound0532 : ∀ pen last, terminalScore 532 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 532).parity (tailData 532 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 532 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0975
  · exact terminalBound0947
  · exact terminalBound0976
  · exact terminalBound0949
theorem nodeIntegerBound0533 : ∀ pen last, terminalScore 533 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 533).parity (tailData 533 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 533 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0815
  · exact terminalBound0943
  · exact terminalBound0977
  · exact terminalBound0405
theorem nodeIntegerBound0534 : ∀ pen last, terminalScore 534 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 534).parity (tailData 534 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 534 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0978
  · exact terminalBound0919
  · exact terminalBound0819
  · exact terminalBound0919
theorem nodeIntegerBound0535 : ∀ pen last, terminalScore 535 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 535).parity (tailData 535 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 535 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0979
  · exact terminalBound0955
  · exact terminalBound0980
  · exact terminalBound0964
theorem nodeIntegerBound0536 : ∀ pen last, terminalScore 536 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 536).parity (tailData 536 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 536 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0981
  · exact terminalBound0945
  · exact terminalBound0974
  · exact terminalBound0937
theorem nodeIntegerBound0537 : ∀ pen last, terminalScore 537 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 537).parity (tailData 537 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 537 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0982
  · exact terminalBound0943
  · exact terminalBound0977
  · exact terminalBound0405
theorem nodeIntegerBound0538 : ∀ pen last, terminalScore 538 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 538).parity (tailData 538 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 538 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0983
  · exact terminalBound0933
  · exact terminalBound0984
  · exact terminalBound0961
theorem nodeIntegerBound0539 : ∀ pen last, terminalScore 539 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 539).parity (tailData 539 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 539 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0815
  · exact terminalBound0943
  · exact terminalBound0977
  · exact terminalBound0405
theorem nodeIntegerBound0540 : ∀ pen last, terminalScore 540 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 540).parity (tailData 540 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 540 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0985
  · exact terminalBound0943
  · exact terminalBound0977
  · exact terminalBound0405
theorem nodeIntegerBound0541 : ∀ pen last, terminalScore 541 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 541).parity (tailData 541 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 541 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0315
  · exact terminalBound0413
  · exact terminalBound0423
  · exact terminalBound0109
theorem nodeIntegerBound0542 : ∀ pen last, terminalScore 542 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 542).parity (tailData 542 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 542 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0986
  · exact terminalBound0921
  · exact terminalBound0987
  · exact terminalBound0923
theorem nodeIntegerBound0543 : ∀ pen last, terminalScore 543 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 543).parity (tailData 543 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 543 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0986
  · exact terminalBound0921
  · exact terminalBound0988
  · exact terminalBound0933
theorem nodeIntegerBound0544 : ∀ pen last, terminalScore 544 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 544).parity (tailData 544 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 544 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0838
  · exact terminalBound0921
  · exact terminalBound0989
  · exact terminalBound0923
theorem nodeIntegerBound0545 : ∀ pen last, terminalScore 545 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 545).parity (tailData 545 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 545 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0986
  · exact terminalBound0921
  · exact terminalBound0990
  · exact terminalBound0961
theorem nodeIntegerBound0546 : ∀ pen last, terminalScore 546 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 546).parity (tailData 546 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 546 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0975
  · exact terminalBound0947
  · exact terminalBound0991
  · exact terminalBound0949
theorem nodeIntegerBound0547 : ∀ pen last, terminalScore 547 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 547).parity (tailData 547 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 547 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0992
  · exact terminalBound0957
  · exact terminalBound0993
  · exact terminalBound0949
theorem nodeIntegerBound0548 : ∀ pen last, terminalScore 548 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 548).parity (tailData 548 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 548 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0815
  · exact terminalBound0943
  · exact terminalBound0977
  · exact terminalBound0405
theorem nodeIntegerBound0549 : ∀ pen last, terminalScore 549 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 549).parity (tailData 549 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 549 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0994
  · exact terminalBound0957
  · exact terminalBound0991
  · exact terminalBound0949
theorem nodeIntegerBound0550 : ∀ pen last, terminalScore 550 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 550).parity (tailData 550 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 550 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0995
  · exact terminalBound0943
  · exact terminalBound0427
  · exact terminalBound0405
theorem nodeIntegerBound0551 : ∀ pen last, terminalScore 551 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 551).parity (tailData 551 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 551 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0429
  · exact terminalBound0395
  · exact terminalBound0849
  · exact terminalBound0395
theorem nodeIntegerBound0552 : ∀ pen last, terminalScore 552 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 552).parity (tailData 552 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 552 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0983
  · exact terminalBound0933
  · exact terminalBound0989
  · exact terminalBound0923
theorem nodeIntegerBound0553 : ∀ pen last, terminalScore 553 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 553).parity (tailData 553 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 553 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0985
  · exact terminalBound0943
  · exact terminalBound0815
  · exact terminalBound0943
theorem nodeIntegerBound0554 : ∀ pen last, terminalScore 554 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 554).parity (tailData 554 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 554 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0815
  · exact terminalBound0943
  · exact terminalBound0977
  · exact terminalBound0405
theorem nodeIntegerBound0555 : ∀ pen last, terminalScore 555 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 555).parity (tailData 555 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 555 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0996
  · exact terminalBound0943
  · exact terminalBound0977
  · exact terminalBound0405
theorem nodeIntegerBound0556 : ∀ pen last, terminalScore 556 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 556).parity (tailData 556 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 556 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0978
  · exact terminalBound0919
  · exact terminalBound0997
  · exact terminalBound0391
theorem nodeIntegerBound0557 : ∀ pen last, terminalScore 557 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 557).parity (tailData 557 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 557 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0978
  · exact terminalBound0919
  · exact terminalBound0998
  · exact terminalBound0393
theorem nodeIntegerBound0558 : ∀ pen last, terminalScore 558 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 558).parity (tailData 558 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 558 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0849
  · exact terminalBound0395
  · exact terminalBound0436
  · exact terminalBound0387
theorem nodeIntegerBound0559 : ∀ pen last, terminalScore 559 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 559).parity (tailData 559 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 559 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0999
  · exact terminalBound0933
  · exact terminalBound0989
  · exact terminalBound0923
theorem nodeIntegerBound0560 : ∀ pen last, terminalScore 560 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 560).parity (tailData 560 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 560 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0819
  · exact terminalBound0919
  · exact terminalBound0997
  · exact terminalBound0391
theorem nodeIntegerBound0561 : ∀ pen last, terminalScore 561 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 561).parity (tailData 561 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 561 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0983
  · exact terminalBound0933
  · exact terminalBound0989
  · exact terminalBound0923
theorem nodeIntegerBound0562 : ∀ pen last, terminalScore 562 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 562).parity (tailData 562 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 562 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0849
  · exact terminalBound0395
  · exact terminalBound0436
  · exact terminalBound0387
theorem nodeIntegerBound0563 : ∀ pen last, terminalScore 563 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 563).parity (tailData 563 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 563 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0442
  · exact terminalBound0443
  · exact terminalBound1000
  · exact terminalBound0443
theorem nodeIntegerBound0564 : ∀ pen last, terminalScore 564 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 564).parity (tailData 564 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 564 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1001
  · exact terminalBound1002
  · exact terminalBound1003
  · exact terminalBound1004
theorem nodeIntegerBound0565 : ∀ pen last, terminalScore 565 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 565).parity (tailData 565 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 565 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1005
  · exact terminalBound1006
  · exact terminalBound1007
  · exact terminalBound1008
theorem nodeIntegerBound0566 : ∀ pen last, terminalScore 566 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 566).parity (tailData 566 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 566 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1009
  · exact terminalBound1006
  · exact terminalBound1010
  · exact terminalBound1011
theorem nodeIntegerBound0567 : ∀ pen last, terminalScore 567 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 567).parity (tailData 567 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 567 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1012
  · exact terminalBound1002
  · exact terminalBound1003
  · exact terminalBound1004
theorem nodeIntegerBound0568 : ∀ pen last, terminalScore 568 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 568).parity (tailData 568 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 568 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1013
  · exact terminalBound1014
  · exact terminalBound1015
  · exact terminalBound1016
theorem nodeIntegerBound0569 : ∀ pen last, terminalScore 569 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 569).parity (tailData 569 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 569 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1009
  · exact terminalBound1006
  · exact terminalBound1007
  · exact terminalBound1008
theorem nodeIntegerBound0570 : ∀ pen last, terminalScore 570 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 570).parity (tailData 570 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 570 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1001
  · exact terminalBound1002
  · exact terminalBound1003
  · exact terminalBound1004
theorem nodeIntegerBound0571 : ∀ pen last, terminalScore 571 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 571).parity (tailData 571 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 571 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0983
  · exact terminalBound0933
  · exact terminalBound0869
  · exact terminalBound1017
theorem nodeIntegerBound0572 : ∀ pen last, terminalScore 572 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 572).parity (tailData 572 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 572 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1012
  · exact terminalBound1002
  · exact terminalBound1003
  · exact terminalBound1004
theorem nodeIntegerBound0573 : ∀ pen last, terminalScore 573 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 573).parity (tailData 573 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 573 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1018
  · exact terminalBound1002
  · exact terminalBound1003
  · exact terminalBound1004
theorem nodeIntegerBound0574 : ∀ pen last, terminalScore 574 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 574).parity (tailData 574 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 574 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0446
  · exact terminalBound0447
  · exact terminalBound0448
  · exact terminalBound0449
theorem nodeIntegerBound0575 : ∀ pen last, terminalScore 575 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 575).parity (tailData 575 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 575 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0978
  · exact terminalBound0919
  · exact terminalBound1019
  · exact terminalBound0407
theorem nodeIntegerBound0576 : ∀ pen last, terminalScore 576 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 576).parity (tailData 576 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 576 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0981
  · exact terminalBound0945
  · exact terminalBound0974
  · exact terminalBound0937
theorem nodeIntegerBound0577 : ∀ pen last, terminalScore 577 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 577).parity (tailData 577 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 577 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1020
  · exact terminalBound0955
  · exact terminalBound1021
  · exact terminalBound0941
theorem nodeIntegerBound0578 : ∀ pen last, terminalScore 578 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 578).parity (tailData 578 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 578 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0815
  · exact terminalBound0943
  · exact terminalBound0977
  · exact terminalBound0405
theorem nodeIntegerBound0579 : ∀ pen last, terminalScore 579 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 579).parity (tailData 579 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 579 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0981
  · exact terminalBound0945
  · exact terminalBound0876
  · exact terminalBound1022
theorem nodeIntegerBound0580 : ∀ pen last, terminalScore 580 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 580).parity (tailData 580 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 580 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1023
  · exact terminalBound1024
  · exact terminalBound1025
  · exact terminalBound1026
theorem nodeIntegerBound0581 : ∀ pen last, terminalScore 581 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 581).parity (tailData 581 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 581 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1027
  · exact terminalBound1028
  · exact terminalBound1029
  · exact terminalBound1030
theorem nodeIntegerBound0582 : ∀ pen last, terminalScore 582 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 582).parity (tailData 582 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 582 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1031
  · exact terminalBound1032
  · exact terminalBound1033
  · exact terminalBound1034
theorem nodeIntegerBound0583 : ∀ pen last, terminalScore 583 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 583).parity (tailData 583 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 583 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1035
  · exact terminalBound1024
  · exact terminalBound1025
  · exact terminalBound1026
theorem nodeIntegerBound0584 : ∀ pen last, terminalScore 584 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 584).parity (tailData 584 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 584 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1036
  · exact terminalBound0455
  · exact terminalBound0456
  · exact terminalBound0457
theorem nodeIntegerBound0585 : ∀ pen last, terminalScore 585 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 585).parity (tailData 585 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 585 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0458
  · exact terminalBound0459
  · exact terminalBound1037
  · exact terminalBound0459
theorem nodeIntegerBound0586 : ∀ pen last, terminalScore 586 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 586).parity (tailData 586 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 586 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1038
  · exact terminalBound1039
  · exact terminalBound1040
  · exact terminalBound1041
theorem nodeIntegerBound0587 : ∀ pen last, terminalScore 587 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 587).parity (tailData 587 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 587 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1042
  · exact terminalBound1043
  · exact terminalBound1044
  · exact terminalBound1043
theorem nodeIntegerBound0588 : ∀ pen last, terminalScore 588 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 588).parity (tailData 588 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 588 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1045
  · exact terminalBound1024
  · exact terminalBound1025
  · exact terminalBound1026
theorem nodeIntegerBound0589 : ∀ pen last, terminalScore 589 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 589).parity (tailData 589 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 589 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1038
  · exact terminalBound1039
  · exact terminalBound1046
  · exact terminalBound1047
theorem nodeIntegerBound0590 : ∀ pen last, terminalScore 590 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 590).parity (tailData 590 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 590 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1023
  · exact terminalBound1024
  · exact terminalBound1025
  · exact terminalBound1026
theorem nodeIntegerBound0591 : ∀ pen last, terminalScore 591 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 591).parity (tailData 591 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 591 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1042
  · exact terminalBound1043
  · exact terminalBound1048
  · exact terminalBound1049
theorem nodeIntegerBound0592 : ∀ pen last, terminalScore 592 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 592).parity (tailData 592 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 592 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1036
  · exact terminalBound0455
  · exact terminalBound0456
  · exact terminalBound0457
theorem nodeIntegerBound0593 : ∀ pen last, terminalScore 593 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 593).parity (tailData 593 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 593 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1050
  · exact terminalBound1051
  · exact terminalBound1052
  · exact terminalBound1051
theorem nodeIntegerBound0594 : ∀ pen last, terminalScore 594 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 594).parity (tailData 594 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 594 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1053
  · exact terminalBound1024
  · exact terminalBound1025
  · exact terminalBound1026
theorem nodeIntegerBound0595 : ∀ pen last, terminalScore 595 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 595).parity (tailData 595 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 595 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1050
  · exact terminalBound1051
  · exact terminalBound1054
  · exact terminalBound1055
theorem nodeIntegerBound0596 : ∀ pen last, terminalScore 596 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 596).parity (tailData 596 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 596 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1036
  · exact terminalBound0455
  · exact terminalBound0456
  · exact terminalBound0457
theorem nodeIntegerBound0597 : ∀ pen last, terminalScore 597 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 597).parity (tailData 597 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 597 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0469
  · exact terminalBound0470
  · exact terminalBound1056
  · exact terminalBound0470
theorem nodeIntegerBound0598 : ∀ pen last, terminalScore 598 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 598).parity (tailData 598 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 598 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1057
  · exact terminalBound1051
  · exact terminalBound1058
  · exact terminalBound1059
theorem nodeIntegerBound0599 : ∀ pen last, terminalScore 599 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 599).parity (tailData 599 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 599 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1027
  · exact terminalBound1028
  · exact terminalBound1060
  · exact terminalBound1061
theorem nodeIntegerBound0600 : ∀ pen last, terminalScore 600 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 600).parity (tailData 600 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 600 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1027
  · exact terminalBound1028
  · exact terminalBound1062
  · exact terminalBound1063
theorem nodeIntegerBound0601 : ∀ pen last, terminalScore 601 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 601).parity (tailData 601 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 601 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1052
  · exact terminalBound1051
  · exact terminalBound1058
  · exact terminalBound1059
theorem nodeIntegerBound0602 : ∀ pen last, terminalScore 602 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 602).parity (tailData 602 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 602 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1064
  · exact terminalBound1065
  · exact terminalBound1066
  · exact terminalBound1067
theorem nodeIntegerBound0603 : ∀ pen last, terminalScore 603 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 603).parity (tailData 603 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 603 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1068
  · exact terminalBound1024
  · exact terminalBound1025
  · exact terminalBound1026
theorem nodeIntegerBound0604 : ∀ pen last, terminalScore 604 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 604).parity (tailData 604 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 604 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1027
  · exact terminalBound1028
  · exact terminalBound1069
  · exact terminalBound1070
theorem nodeIntegerBound0605 : ∀ pen last, terminalScore 605 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 605).parity (tailData 605 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 605 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1071
  · exact terminalBound1065
  · exact terminalBound1066
  · exact terminalBound1067
theorem nodeIntegerBound0606 : ∀ pen last, terminalScore 606 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 606).parity (tailData 606 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 606 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1072
  · exact terminalBound1032
  · exact terminalBound1031
  · exact terminalBound1032
theorem nodeIntegerBound0607 : ∀ pen last, terminalScore 607 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 607).parity (tailData 607 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 607 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1068
  · exact terminalBound1024
  · exact terminalBound1025
  · exact terminalBound1026
theorem nodeIntegerBound0608 : ∀ pen last, terminalScore 608 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 608).parity (tailData 608 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 608 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1072
  · exact terminalBound1032
  · exact terminalBound1033
  · exact terminalBound1034
theorem nodeIntegerBound0609 : ∀ pen last, terminalScore 609 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 609).parity (tailData 609 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 609 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0476
  · exact terminalBound0455
  · exact terminalBound0456
  · exact terminalBound0457
theorem nodeIntegerBound0610 : ∀ pen last, terminalScore 610 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 610).parity (tailData 610 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 610 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1050
  · exact terminalBound1051
  · exact terminalBound1058
  · exact terminalBound1059
theorem nodeIntegerBound0611 : ∀ pen last, terminalScore 611 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 611).parity (tailData 611 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 611 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1052
  · exact terminalBound1051
  · exact terminalBound1058
  · exact terminalBound1059
theorem nodeIntegerBound0612 : ∀ pen last, terminalScore 612 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 612).parity (tailData 612 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 612 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1035
  · exact terminalBound1024
  · exact terminalBound1025
  · exact terminalBound1026
theorem nodeIntegerBound0613 : ∀ pen last, terminalScore 613 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 613).parity (tailData 613 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 613 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0466
  · exact terminalBound0455
  · exact terminalBound1036
  · exact terminalBound0455
theorem nodeIntegerBound0614 : ∀ pen last, terminalScore 614 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 614).parity (tailData 614 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 614 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1036
  · exact terminalBound0455
  · exact terminalBound0456
  · exact terminalBound0457
theorem nodeIntegerBound0615 : ∀ pen last, terminalScore 615 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 615).parity (tailData 615 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 615 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1073
  · exact terminalBound1074
  · exact terminalBound1075
  · exact terminalBound1076
theorem nodeIntegerBound0616 : ∀ pen last, terminalScore 616 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 616).parity (tailData 616 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 616 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0495
  · exact terminalBound1077
  · exact terminalBound0495
  · exact terminalBound0496
theorem nodeIntegerBound0617 : ∀ pen last, terminalScore 617 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 617).parity (tailData 617 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 617 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1073
  · exact terminalBound1074
  · exact terminalBound1075
  · exact terminalBound1078
theorem nodeIntegerBound0618 : ∀ pen last, terminalScore 618 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 618).parity (tailData 618 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 618 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0493
  · exact terminalBound0494
  · exact terminalBound0495
  · exact terminalBound0496
theorem nodeIntegerBound0619 : ∀ pen last, terminalScore 619 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 619).parity (tailData 619 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 619 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0497
  · exact terminalBound0498
  · exact terminalBound0495
  · exact terminalBound1077
theorem nodeIntegerBound0620 : ∀ pen last, terminalScore 620 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 620).parity (tailData 620 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 620 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0495
  · exact terminalBound1077
  · exact terminalBound0495
  · exact terminalBound0496
theorem nodeIntegerBound0621 : ∀ pen last, terminalScore 621 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 621).parity (tailData 621 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 621 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1079
  · exact terminalBound1080
  · exact terminalBound1081
  · exact terminalBound1082
theorem nodeIntegerBound0622 : ∀ pen last, terminalScore 622 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 622).parity (tailData 622 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 622 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0495
  · exact terminalBound1077
  · exact terminalBound0495
  · exact terminalBound0496
theorem nodeIntegerBound0623 : ∀ pen last, terminalScore 623 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 623).parity (tailData 623 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 623 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1073
  · exact terminalBound1074
  · exact terminalBound1075
  · exact terminalBound1083
theorem nodeIntegerBound0624 : ∀ pen last, terminalScore 624 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 624).parity (tailData 624 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 624 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1084
  · exact terminalBound1085
  · exact terminalBound1086
  · exact terminalBound1087
theorem nodeIntegerBound0625 : ∀ pen last, terminalScore 625 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 625).parity (tailData 625 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 625 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1073
  · exact terminalBound1074
  · exact terminalBound1075
  · exact terminalBound1088
theorem nodeIntegerBound0626 : ∀ pen last, terminalScore 626 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 626).parity (tailData 626 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 626 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0514
  · exact terminalBound1089
  · exact terminalBound0514
  · exact terminalBound0515
theorem nodeIntegerBound0627 : ∀ pen last, terminalScore 627 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 627).parity (tailData 627 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 627 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1090
  · exact terminalBound1091
  · exact terminalBound1086
  · exact terminalBound1087
theorem nodeIntegerBound0628 : ∀ pen last, terminalScore 628 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 628).parity (tailData 628 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 628 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0502
  · exact terminalBound0511
  · exact terminalBound0502
  · exact terminalBound0503
theorem nodeIntegerBound0629 : ∀ pen last, terminalScore 629 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 629).parity (tailData 629 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 629 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1092
  · exact terminalBound1093
  · exact terminalBound1094
  · exact terminalBound1095
theorem nodeIntegerBound0630 : ∀ pen last, terminalScore 630 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 630).parity (tailData 630 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 630 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1086
  · exact terminalBound1096
  · exact terminalBound1086
  · exact terminalBound1087
theorem nodeIntegerBound0631 : ∀ pen last, terminalScore 631 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 631).parity (tailData 631 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 631 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1097
  · exact terminalBound1098
  · exact terminalBound1099
  · exact terminalBound1100
theorem nodeIntegerBound0632 : ∀ pen last, terminalScore 632 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 632).parity (tailData 632 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 632 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1084
  · exact terminalBound1085
  · exact terminalBound1086
  · exact terminalBound1087
theorem nodeIntegerBound0633 : ∀ pen last, terminalScore 633 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 633).parity (tailData 633 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 633 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1079
  · exact terminalBound1080
  · exact terminalBound1081
  · exact terminalBound1101
theorem nodeIntegerBound0634 : ∀ pen last, terminalScore 634 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 634).parity (tailData 634 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 634 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1086
  · exact terminalBound1096
  · exact terminalBound1086
  · exact terminalBound1087
theorem nodeIntegerBound0635 : ∀ pen last, terminalScore 635 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 635).parity (tailData 635 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 635 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1097
  · exact terminalBound1098
  · exact terminalBound1099
  · exact terminalBound1102
theorem nodeIntegerBound0636 : ∀ pen last, terminalScore 636 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 636).parity (tailData 636 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 636 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1086
  · exact terminalBound1096
  · exact terminalBound1086
  · exact terminalBound1087
theorem nodeIntegerBound0637 : ∀ pen last, terminalScore 637 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 637).parity (tailData 637 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 637 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1090
  · exact terminalBound1091
  · exact terminalBound1086
  · exact terminalBound1096
theorem nodeIntegerBound0638 : ∀ pen last, terminalScore 638 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 638).parity (tailData 638 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 638 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1086
  · exact terminalBound1096
  · exact terminalBound1086
  · exact terminalBound1087
theorem nodeIntegerBound0639 : ∀ pen last, terminalScore 639 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 639).parity (tailData 639 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 639 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1103
  · exact terminalBound1104
  · exact terminalBound1086
  · exact terminalBound1087

end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
