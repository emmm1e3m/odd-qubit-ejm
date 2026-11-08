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

theorem nodeIntegerBound1024 : ∀ pen last, terminalScore 1024 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1024).parity (tailData 1024 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1024 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1435
  · exact terminalBound1514
  · exact terminalBound1542
  · exact terminalBound1543
theorem nodeIntegerBound1025 : ∀ pen last, terminalScore 1025 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1025).parity (tailData 1025 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1025 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1454
  · exact terminalBound1544
  · exact terminalBound1456
  · exact terminalBound1547
theorem nodeIntegerBound1026 : ∀ pen last, terminalScore 1026 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1026).parity (tailData 1026 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1026 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1500
  · exact terminalBound1501
  · exact terminalBound1502
  · exact terminalBound1503
theorem nodeIntegerBound1027 : ∀ pen last, terminalScore 1027 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1027).parity (tailData 1027 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1027 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1515
  · exact terminalBound1516
  · exact terminalBound1502
  · exact terminalBound1503
theorem nodeIntegerBound1028 : ∀ pen last, terminalScore 1028 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1028).parity (tailData 1028 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1028 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1548
  · exact terminalBound1549
  · exact terminalBound1542
  · exact terminalBound1543
theorem nodeIntegerBound1029 : ∀ pen last, terminalScore 1029 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1029).parity (tailData 1029 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1029 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0926
  · exact terminalBound0927
  · exact terminalBound1550
  · exact terminalBound1551
theorem nodeIntegerBound1030 : ∀ pen last, terminalScore 1030 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1030).parity (tailData 1030 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1030 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1552
  · exact terminalBound1553
  · exact terminalBound1554
  · exact terminalBound1555
theorem nodeIntegerBound1031 : ∀ pen last, terminalScore 1031 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1031).parity (tailData 1031 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1031 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1550
  · exact terminalBound1551
  · exact terminalBound0928
  · exact terminalBound0929
theorem nodeIntegerBound1032 : ∀ pen last, terminalScore 1032 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1032).parity (tailData 1032 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1032 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1556
  · exact terminalBound1557
  · exact terminalBound1554
  · exact terminalBound1555
theorem nodeIntegerBound1033 : ∀ pen last, terminalScore 1033 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1033).parity (tailData 1033 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1033 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0932
  · exact terminalBound0933
  · exact terminalBound0922
  · exact terminalBound0923
theorem nodeIntegerBound1034 : ∀ pen last, terminalScore 1034 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1034).parity (tailData 1034 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1034 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1556
  · exact terminalBound1557
  · exact terminalBound1554
  · exact terminalBound1555
theorem nodeIntegerBound1035 : ∀ pen last, terminalScore 1035 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1035).parity (tailData 1035 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1035 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1558
  · exact terminalBound1559
  · exact terminalBound1560
  · exact terminalBound1561
theorem nodeIntegerBound1036 : ∀ pen last, terminalScore 1036 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1036).parity (tailData 1036 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1036 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1562
  · exact terminalBound1563
  · exact terminalBound1554
  · exact terminalBound1555
theorem nodeIntegerBound1037 : ∀ pen last, terminalScore 1037 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1037).parity (tailData 1037 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1037 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1558
  · exact terminalBound1559
  · exact terminalBound1564
  · exact terminalBound1565
theorem nodeIntegerBound1038 : ∀ pen last, terminalScore 1038 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1038).parity (tailData 1038 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1038 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1552
  · exact terminalBound1553
  · exact terminalBound1554
  · exact terminalBound1555
theorem nodeIntegerBound1039 : ∀ pen last, terminalScore 1039 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1039).parity (tailData 1039 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1039 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1556
  · exact terminalBound1557
  · exact terminalBound1562
  · exact terminalBound1563
theorem nodeIntegerBound1040 : ∀ pen last, terminalScore 1040 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1040).parity (tailData 1040 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1040 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1562
  · exact terminalBound1563
  · exact terminalBound1554
  · exact terminalBound1555
theorem nodeIntegerBound1041 : ∀ pen last, terminalScore 1041 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1041).parity (tailData 1041 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1041 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1566
  · exact terminalBound1567
  · exact terminalBound1568
  · exact terminalBound1569
theorem nodeIntegerBound1042 : ∀ pen last, terminalScore 1042 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1042).parity (tailData 1042 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1042 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1570
  · exact terminalBound1571
  · exact terminalBound1572
  · exact terminalBound1573
theorem nodeIntegerBound1043 : ∀ pen last, terminalScore 1043 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1043).parity (tailData 1043 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1043 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1574
  · exact terminalBound1575
  · exact terminalBound0948
  · exact terminalBound0949
theorem nodeIntegerBound1044 : ∀ pen last, terminalScore 1044 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1044).parity (tailData 1044 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1044 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1576
  · exact terminalBound1577
  · exact terminalBound1578
  · exact terminalBound1579
theorem nodeIntegerBound1045 : ∀ pen last, terminalScore 1045 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1045).parity (tailData 1045 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1045 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1570
  · exact terminalBound1571
  · exact terminalBound1568
  · exact terminalBound1569
theorem nodeIntegerBound1046 : ∀ pen last, terminalScore 1046 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1046).parity (tailData 1046 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1046 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0956
  · exact terminalBound0957
  · exact terminalBound0948
  · exact terminalBound0949
theorem nodeIntegerBound1047 : ∀ pen last, terminalScore 1047 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1047).parity (tailData 1047 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1047 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1556
  · exact terminalBound1557
  · exact terminalBound1580
  · exact terminalBound1581
theorem nodeIntegerBound1048 : ∀ pen last, terminalScore 1048 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1048).parity (tailData 1048 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1048 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1574
  · exact terminalBound1575
  · exact terminalBound0948
  · exact terminalBound0949
theorem nodeIntegerBound1049 : ∀ pen last, terminalScore 1049 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1049).parity (tailData 1049 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1049 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1558
  · exact terminalBound1559
  · exact terminalBound1582
  · exact terminalBound1583
theorem nodeIntegerBound1050 : ∀ pen last, terminalScore 1050 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1050).parity (tailData 1050 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1050 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1584
  · exact terminalBound1585
  · exact terminalBound1586
  · exact terminalBound1587
theorem nodeIntegerBound1051 : ∀ pen last, terminalScore 1051 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1051).parity (tailData 1051 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1051 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1558
  · exact terminalBound1559
  · exact terminalBound1588
  · exact terminalBound1589
theorem nodeIntegerBound1052 : ∀ pen last, terminalScore 1052 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1052).parity (tailData 1052 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1052 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1590
  · exact terminalBound1591
  · exact terminalBound1568
  · exact terminalBound1569
theorem nodeIntegerBound1053 : ∀ pen last, terminalScore 1053 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1053).parity (tailData 1053 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1053 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1592
  · exact terminalBound1593
  · exact terminalBound1586
  · exact terminalBound1587
theorem nodeIntegerBound1054 : ∀ pen last, terminalScore 1054 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1054).parity (tailData 1054 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1054 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1574
  · exact terminalBound1575
  · exact terminalBound0948
  · exact terminalBound0949
theorem nodeIntegerBound1055 : ∀ pen last, terminalScore 1055 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1055).parity (tailData 1055 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1055 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1570
  · exact terminalBound1571
  · exact terminalBound1590
  · exact terminalBound1591
theorem nodeIntegerBound1056 : ∀ pen last, terminalScore 1056 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1056).parity (tailData 1056 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1056 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1594
  · exact terminalBound1595
  · exact terminalBound1586
  · exact terminalBound1587
theorem nodeIntegerBound1057 : ∀ pen last, terminalScore 1057 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1057).parity (tailData 1057 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1057 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1596
  · exact terminalBound1597
  · exact terminalBound1586
  · exact terminalBound1587
theorem nodeIntegerBound1058 : ∀ pen last, terminalScore 1058 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1058).parity (tailData 1058 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1058 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1594
  · exact terminalBound1595
  · exact terminalBound1586
  · exact terminalBound1587
theorem nodeIntegerBound1059 : ∀ pen last, terminalScore 1059 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1059).parity (tailData 1059 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1059 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1598
  · exact terminalBound1599
  · exact terminalBound1578
  · exact terminalBound1579
theorem nodeIntegerBound1060 : ∀ pen last, terminalScore 1060 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1060).parity (tailData 1060 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1060 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1592
  · exact terminalBound1593
  · exact terminalBound1586
  · exact terminalBound1587
theorem nodeIntegerBound1061 : ∀ pen last, terminalScore 1061 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1061).parity (tailData 1061 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1061 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0952
  · exact terminalBound0953
  · exact terminalBound1574
  · exact terminalBound1575
theorem nodeIntegerBound1062 : ∀ pen last, terminalScore 1062 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1062).parity (tailData 1062 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1062 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1574
  · exact terminalBound1575
  · exact terminalBound0948
  · exact terminalBound0949
theorem nodeIntegerBound1063 : ∀ pen last, terminalScore 1063 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1063).parity (tailData 1063 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1063 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1600
  · exact terminalBound1567
  · exact terminalBound1601
  · exact terminalBound1569
theorem nodeIntegerBound1064 : ∀ pen last, terminalScore 1064 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1064).parity (tailData 1064 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1064 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1602
  · exact terminalBound1577
  · exact terminalBound1603
  · exact terminalBound1604
theorem nodeIntegerBound1065 : ∀ pen last, terminalScore 1065 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1065).parity (tailData 1065 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1065 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1605
  · exact terminalBound1575
  · exact terminalBound0967
  · exact terminalBound0949
theorem nodeIntegerBound1066 : ∀ pen last, terminalScore 1066 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1066).parity (tailData 1066 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1066 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1600
  · exact terminalBound1567
  · exact terminalBound1606
  · exact terminalBound1591
theorem nodeIntegerBound1067 : ∀ pen last, terminalScore 1067 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1067).parity (tailData 1067 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1067 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1607
  · exact terminalBound1585
  · exact terminalBound1608
  · exact terminalBound1587
theorem nodeIntegerBound1068 : ∀ pen last, terminalScore 1068 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1068).parity (tailData 1068 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1068 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1558
  · exact terminalBound1559
  · exact terminalBound1609
  · exact terminalBound1589
theorem nodeIntegerBound1069 : ∀ pen last, terminalScore 1069 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1069).parity (tailData 1069 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1069 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1606
  · exact terminalBound1591
  · exact terminalBound1601
  · exact terminalBound1569
theorem nodeIntegerBound1070 : ∀ pen last, terminalScore 1070 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1070).parity (tailData 1070 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1070 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1610
  · exact terminalBound1597
  · exact terminalBound1608
  · exact terminalBound1587
theorem nodeIntegerBound1071 : ∀ pen last, terminalScore 1071 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1071).parity (tailData 1071 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1071 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1605
  · exact terminalBound1575
  · exact terminalBound0967
  · exact terminalBound0949
theorem nodeIntegerBound1072 : ∀ pen last, terminalScore 1072 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1072).parity (tailData 1072 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1072 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1602
  · exact terminalBound1577
  · exact terminalBound1611
  · exact terminalBound1599
theorem nodeIntegerBound1073 : ∀ pen last, terminalScore 1073 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1073).parity (tailData 1073 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1073 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1612
  · exact terminalBound1595
  · exact terminalBound1608
  · exact terminalBound1587
theorem nodeIntegerBound1074 : ∀ pen last, terminalScore 1074 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1074).parity (tailData 1074 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1074 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1607
  · exact terminalBound1585
  · exact terminalBound1608
  · exact terminalBound1587
theorem nodeIntegerBound1075 : ∀ pen last, terminalScore 1075 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1075).parity (tailData 1075 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1075 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1613
  · exact terminalBound1593
  · exact terminalBound1608
  · exact terminalBound1587
theorem nodeIntegerBound1076 : ∀ pen last, terminalScore 1076 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1076).parity (tailData 1076 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1076 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1556
  · exact terminalBound1557
  · exact terminalBound1614
  · exact terminalBound1581
theorem nodeIntegerBound1077 : ∀ pen last, terminalScore 1077 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1077).parity (tailData 1077 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1077 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1605
  · exact terminalBound1575
  · exact terminalBound0967
  · exact terminalBound0949
theorem nodeIntegerBound1078 : ∀ pen last, terminalScore 1078 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1078).parity (tailData 1078 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1078 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1615
  · exact terminalBound1593
  · exact terminalBound1616
  · exact terminalBound1587
theorem nodeIntegerBound1079 : ∀ pen last, terminalScore 1079 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1079).parity (tailData 1079 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1079 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1617
  · exact terminalBound1591
  · exact terminalBound1618
  · exact terminalBound1573
theorem nodeIntegerBound1080 : ∀ pen last, terminalScore 1080 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1080).parity (tailData 1080 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1080 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1438
  · exact terminalBound1575
  · exact terminalBound1619
  · exact terminalBound0949
theorem nodeIntegerBound1081 : ∀ pen last, terminalScore 1081 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1081).parity (tailData 1081 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1081 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1620
  · exact terminalBound1553
  · exact terminalBound1621
  · exact terminalBound1563
theorem nodeIntegerBound1082 : ∀ pen last, terminalScore 1082 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1082).parity (tailData 1082 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1082 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1622
  · exact terminalBound1585
  · exact terminalBound1623
  · exact terminalBound1587
theorem nodeIntegerBound1083 : ∀ pen last, terminalScore 1083 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1083).parity (tailData 1083 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1083 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1624
  · exact terminalBound1585
  · exact terminalBound1616
  · exact terminalBound1587
theorem nodeIntegerBound1084 : ∀ pen last, terminalScore 1084 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1084).parity (tailData 1084 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1084 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1445
  · exact terminalBound0947
  · exact terminalBound1619
  · exact terminalBound0949
theorem nodeIntegerBound1085 : ∀ pen last, terminalScore 1085 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1085).parity (tailData 1085 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1085 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1625
  · exact terminalBound1563
  · exact terminalBound1626
  · exact terminalBound1581
theorem nodeIntegerBound1086 : ∀ pen last, terminalScore 1086 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1086).parity (tailData 1086 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1086 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1438
  · exact terminalBound1575
  · exact terminalBound1619
  · exact terminalBound0949
theorem nodeIntegerBound1087 : ∀ pen last, terminalScore 1087 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1087).parity (tailData 1087 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1087 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1627
  · exact terminalBound1575
  · exact terminalBound1619
  · exact terminalBound0949
theorem nodeIntegerBound1088 : ∀ pen last, terminalScore 1088 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1088).parity (tailData 1088 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1088 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0815
  · exact terminalBound0943
  · exact terminalBound0977
  · exact terminalBound0405
theorem nodeIntegerBound1089 : ∀ pen last, terminalScore 1089 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1089).parity (tailData 1089 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1089 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1628
  · exact terminalBound1551
  · exact terminalBound1629
  · exact terminalBound0929
theorem nodeIntegerBound1090 : ∀ pen last, terminalScore 1090 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1090).parity (tailData 1090 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1090 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1628
  · exact terminalBound1551
  · exact terminalBound1630
  · exact terminalBound1551
theorem nodeIntegerBound1091 : ∀ pen last, terminalScore 1091 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1091).parity (tailData 1091 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1091 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1631
  · exact terminalBound1563
  · exact terminalBound1632
  · exact terminalBound1555
theorem nodeIntegerBound1092 : ∀ pen last, terminalScore 1092 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1092).parity (tailData 1092 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1092 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1628
  · exact terminalBound1551
  · exact terminalBound1633
  · exact terminalBound0969
theorem nodeIntegerBound1093 : ∀ pen last, terminalScore 1093 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1093).parity (tailData 1093 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1093 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1617
  · exact terminalBound1591
  · exact terminalBound1634
  · exact terminalBound1569
theorem nodeIntegerBound1094 : ∀ pen last, terminalScore 1094 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1094).parity (tailData 1094 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1094 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1635
  · exact terminalBound1599
  · exact terminalBound1636
  · exact terminalBound1604
theorem nodeIntegerBound1095 : ∀ pen last, terminalScore 1095 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1095).parity (tailData 1095 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1095 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1438
  · exact terminalBound1575
  · exact terminalBound1619
  · exact terminalBound0949
theorem nodeIntegerBound1096 : ∀ pen last, terminalScore 1096 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1096).parity (tailData 1096 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1096 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1637
  · exact terminalBound1591
  · exact terminalBound1634
  · exact terminalBound1569
theorem nodeIntegerBound1097 : ∀ pen last, terminalScore 1097 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1097).parity (tailData 1097 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1097 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1458
  · exact terminalBound0955
  · exact terminalBound0980
  · exact terminalBound0964
theorem nodeIntegerBound1098 : ∀ pen last, terminalScore 1098 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1098).parity (tailData 1098 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1098 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0983
  · exact terminalBound0933
  · exact terminalBound1459
  · exact terminalBound0933
theorem nodeIntegerBound1099 : ∀ pen last, terminalScore 1099 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1099).parity (tailData 1099 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1099 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1625
  · exact terminalBound1563
  · exact terminalBound1632
  · exact terminalBound1555
theorem nodeIntegerBound1100 : ∀ pen last, terminalScore 1100 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1100).parity (tailData 1100 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1100 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1627
  · exact terminalBound1575
  · exact terminalBound1438
  · exact terminalBound1575
theorem nodeIntegerBound1101 : ∀ pen last, terminalScore 1101 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1101).parity (tailData 1101 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1101 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1438
  · exact terminalBound1575
  · exact terminalBound1619
  · exact terminalBound0949
theorem nodeIntegerBound1102 : ∀ pen last, terminalScore 1102 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1102).parity (tailData 1102 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1102 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1638
  · exact terminalBound1575
  · exact terminalBound1619
  · exact terminalBound0949
theorem nodeIntegerBound1103 : ∀ pen last, terminalScore 1103 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1103).parity (tailData 1103 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1103 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1620
  · exact terminalBound1553
  · exact terminalBound1639
  · exact terminalBound1555
theorem nodeIntegerBound1104 : ∀ pen last, terminalScore 1104 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1104).parity (tailData 1104 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1104 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1620
  · exact terminalBound1553
  · exact terminalBound1640
  · exact terminalBound1555
theorem nodeIntegerBound1105 : ∀ pen last, terminalScore 1105 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1105).parity (tailData 1105 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1105 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1459
  · exact terminalBound0933
  · exact terminalBound0989
  · exact terminalBound0923
theorem nodeIntegerBound1106 : ∀ pen last, terminalScore 1106 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1106).parity (tailData 1106 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1106 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1641
  · exact terminalBound1553
  · exact terminalBound1632
  · exact terminalBound1555
theorem nodeIntegerBound1107 : ∀ pen last, terminalScore 1107 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1107).parity (tailData 1107 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1107 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1621
  · exact terminalBound1563
  · exact terminalBound1639
  · exact terminalBound1555
theorem nodeIntegerBound1108 : ∀ pen last, terminalScore 1108 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1108).parity (tailData 1108 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1108 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1625
  · exact terminalBound1563
  · exact terminalBound1632
  · exact terminalBound1555
theorem nodeIntegerBound1109 : ∀ pen last, terminalScore 1109 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1109).parity (tailData 1109 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1109 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1459
  · exact terminalBound0933
  · exact terminalBound0989
  · exact terminalBound0923
theorem nodeIntegerBound1110 : ∀ pen last, terminalScore 1110 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1110).parity (tailData 1110 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1110 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0992
  · exact terminalBound0957
  · exact terminalBound1642
  · exact terminalBound1575
theorem nodeIntegerBound1111 : ∀ pen last, terminalScore 1111 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1111).parity (tailData 1111 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1111 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1468
  · exact terminalBound0957
  · exact terminalBound1619
  · exact terminalBound0949
theorem nodeIntegerBound1112 : ∀ pen last, terminalScore 1112 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1112).parity (tailData 1112 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1112 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1643
  · exact terminalBound1595
  · exact terminalBound1644
  · exact terminalBound1587
theorem nodeIntegerBound1113 : ∀ pen last, terminalScore 1113 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1113).parity (tailData 1113 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1113 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1438
  · exact terminalBound1575
  · exact terminalBound1619
  · exact terminalBound0949
theorem nodeIntegerBound1114 : ∀ pen last, terminalScore 1114 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1114).parity (tailData 1114 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1114 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1645
  · exact terminalBound1595
  · exact terminalBound1616
  · exact terminalBound1587
theorem nodeIntegerBound1115 : ∀ pen last, terminalScore 1115 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1115).parity (tailData 1115 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1115 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1643
  · exact terminalBound1595
  · exact terminalBound1623
  · exact terminalBound1587
theorem nodeIntegerBound1116 : ∀ pen last, terminalScore 1116 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1116).parity (tailData 1116 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1116 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1468
  · exact terminalBound0957
  · exact terminalBound1619
  · exact terminalBound0949
theorem nodeIntegerBound1117 : ∀ pen last, terminalScore 1117 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1117).parity (tailData 1117 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1117 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1620
  · exact terminalBound1553
  · exact terminalBound1646
  · exact terminalBound1581
theorem nodeIntegerBound1118 : ∀ pen last, terminalScore 1118 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1118).parity (tailData 1118 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1118 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1624
  · exact terminalBound1585
  · exact terminalBound1616
  · exact terminalBound1587
theorem nodeIntegerBound1119 : ∀ pen last, terminalScore 1119 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1119).parity (tailData 1119 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1119 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1445
  · exact terminalBound0947
  · exact terminalBound1619
  · exact terminalBound0949
theorem nodeIntegerBound1120 : ∀ pen last, terminalScore 1120 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1120).parity (tailData 1120 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1120 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1459
  · exact terminalBound0933
  · exact terminalBound0989
  · exact terminalBound0923
theorem nodeIntegerBound1121 : ∀ pen last, terminalScore 1121 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1121).parity (tailData 1121 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1121 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1627
  · exact terminalBound1575
  · exact terminalBound1619
  · exact terminalBound0949
theorem nodeIntegerBound1122 : ∀ pen last, terminalScore 1122 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1122).parity (tailData 1122 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1122 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1628
  · exact terminalBound1551
  · exact terminalBound1647
  · exact terminalBound0931
theorem nodeIntegerBound1123 : ∀ pen last, terminalScore 1123 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1123).parity (tailData 1123 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1123 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1459
  · exact terminalBound0933
  · exact terminalBound0989
  · exact terminalBound0923
theorem nodeIntegerBound1124 : ∀ pen last, terminalScore 1124 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1124).parity (tailData 1124 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1124 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1628
  · exact terminalBound1551
  · exact terminalBound1629
  · exact terminalBound0929
theorem nodeIntegerBound1125 : ∀ pen last, terminalScore 1125 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1125).parity (tailData 1125 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1125 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound0999
  · exact terminalBound0933
  · exact terminalBound0989
  · exact terminalBound0923
theorem nodeIntegerBound1126 : ∀ pen last, terminalScore 1126 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1126).parity (tailData 1126 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1126 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1630
  · exact terminalBound1551
  · exact terminalBound1629
  · exact terminalBound0929
theorem nodeIntegerBound1127 : ∀ pen last, terminalScore 1127 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1127).parity (tailData 1127 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1127 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1628
  · exact terminalBound1551
  · exact terminalBound1477
  · exact terminalBound1648
theorem nodeIntegerBound1128 : ∀ pen last, terminalScore 1128 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1128).parity (tailData 1128 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1128 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1649
  · exact terminalBound1650
  · exact terminalBound1651
  · exact terminalBound1652
theorem nodeIntegerBound1129 : ∀ pen last, terminalScore 1129 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1129).parity (tailData 1129 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1129 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1628
  · exact terminalBound1551
  · exact terminalBound1482
  · exact terminalBound1653
theorem nodeIntegerBound1130 : ∀ pen last, terminalScore 1130 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1130).parity (tailData 1130 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1130 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1654
  · exact terminalBound1014
  · exact terminalBound1015
  · exact terminalBound1016
theorem nodeIntegerBound1131 : ∀ pen last, terminalScore 1131 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1131).parity (tailData 1131 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1131 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1655
  · exact terminalBound1650
  · exact terminalBound1651
  · exact terminalBound1652
theorem nodeIntegerBound1132 : ∀ pen last, terminalScore 1132 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1132).parity (tailData 1132 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1132 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1012
  · exact terminalBound1002
  · exact terminalBound1003
  · exact terminalBound1004
theorem nodeIntegerBound1133 : ∀ pen last, terminalScore 1133 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1133).parity (tailData 1133 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1133 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1656
  · exact terminalBound1657
  · exact terminalBound1658
  · exact terminalBound1659
theorem nodeIntegerBound1134 : ∀ pen last, terminalScore 1134 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1134).parity (tailData 1134 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1134 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1660
  · exact terminalBound1661
  · exact terminalBound1662
  · exact terminalBound1663
theorem nodeIntegerBound1135 : ∀ pen last, terminalScore 1135 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1135).parity (tailData 1135 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1135 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1664
  · exact terminalBound1650
  · exact terminalBound1651
  · exact terminalBound1652
theorem nodeIntegerBound1136 : ∀ pen last, terminalScore 1136 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1136).parity (tailData 1136 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1136 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1665
  · exact terminalBound1661
  · exact terminalBound1666
  · exact terminalBound1667
theorem nodeIntegerBound1137 : ∀ pen last, terminalScore 1137 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1137).parity (tailData 1137 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1137 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1656
  · exact terminalBound1657
  · exact terminalBound1658
  · exact terminalBound1659
theorem nodeIntegerBound1138 : ∀ pen last, terminalScore 1138 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1138).parity (tailData 1138 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1138 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1649
  · exact terminalBound1650
  · exact terminalBound1651
  · exact terminalBound1652
theorem nodeIntegerBound1139 : ∀ pen last, terminalScore 1139 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1139).parity (tailData 1139 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1139 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1625
  · exact terminalBound1563
  · exact terminalBound1492
  · exact terminalBound1668
theorem nodeIntegerBound1140 : ∀ pen last, terminalScore 1140 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1140).parity (tailData 1140 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1140 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1664
  · exact terminalBound1650
  · exact terminalBound1651
  · exact terminalBound1652
theorem nodeIntegerBound1141 : ∀ pen last, terminalScore 1141 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1141).parity (tailData 1141 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1141 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1660
  · exact terminalBound1661
  · exact terminalBound1666
  · exact terminalBound1667
theorem nodeIntegerBound1142 : ∀ pen last, terminalScore 1142 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1142).parity (tailData 1142 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1142 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1656
  · exact terminalBound1657
  · exact terminalBound1669
  · exact terminalBound1670
theorem nodeIntegerBound1143 : ∀ pen last, terminalScore 1143 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1143).parity (tailData 1143 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1143 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1664
  · exact terminalBound1650
  · exact terminalBound1651
  · exact terminalBound1652
theorem nodeIntegerBound1144 : ∀ pen last, terminalScore 1144 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1144).parity (tailData 1144 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1144 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1655
  · exact terminalBound1650
  · exact terminalBound1664
  · exact terminalBound1650
theorem nodeIntegerBound1145 : ∀ pen last, terminalScore 1145 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1145).parity (tailData 1145 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1145 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1664
  · exact terminalBound1650
  · exact terminalBound1651
  · exact terminalBound1652
theorem nodeIntegerBound1146 : ∀ pen last, terminalScore 1146 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1146).parity (tailData 1146 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1146 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1671
  · exact terminalBound1650
  · exact terminalBound1651
  · exact terminalBound1652
theorem nodeIntegerBound1147 : ∀ pen last, terminalScore 1147 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1147).parity (tailData 1147 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1147 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1020
  · exact terminalBound0955
  · exact terminalBound1458
  · exact terminalBound0955
theorem nodeIntegerBound1148 : ∀ pen last, terminalScore 1148 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1148).parity (tailData 1148 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1148 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1672
  · exact terminalBound1575
  · exact terminalBound1619
  · exact terminalBound0949
theorem nodeIntegerBound1149 : ∀ pen last, terminalScore 1149 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1149).parity (tailData 1149 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1149 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1673
  · exact terminalBound1599
  · exact terminalBound1674
  · exact terminalBound1579
theorem nodeIntegerBound1150 : ∀ pen last, terminalScore 1150 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1150).parity (tailData 1150 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1150 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1617
  · exact terminalBound1591
  · exact terminalBound1634
  · exact terminalBound1569
theorem nodeIntegerBound1151 : ∀ pen last, terminalScore 1151 pen last = 2 →
    8 * trigL1 (terminalCoeffs (nodeData 1151).parity (tailData 1151 pen last).support) ≤
      3 * (64 * (2 : ℤ) ^ (tailData 1151 pen last).exponent) := by
  intro pen last hscore
  cases pen <;> cases last
  · exact terminalBound1672
  · exact terminalBound1575
  · exact terminalBound1619
  · exact terminalBound0949

end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
