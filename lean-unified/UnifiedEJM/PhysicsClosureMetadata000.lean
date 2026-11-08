import UnifiedEJM.PhysicsClosureMetadataDefinition
import UnifiedEJM.PhysicsClosureAggregation

open OddEJM
open scoped BigOperators
namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
open UnifiedEJM.PathCutScore
open UnifiedEJM.ClosureAggregation
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem nodeMetadataSlice000 : FinSlice NodeMetadata 0 64 := by
  intro i hi
  fin_cases i
  · exact (show NodeMetadata (0 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (2 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (3 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (4 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (5 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (6 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (7 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (8 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (9 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (10 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (11 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (12 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (13 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (14 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (15 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (16 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (17 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (18 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (19 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (20 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (21 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (22 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (23 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (24 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (25 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (26 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (27 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (28 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (29 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (30 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (31 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (32 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (33 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (34 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (35 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (36 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (37 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (38 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (39 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (40 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (41 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (42 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (43 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (44 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (45 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (46 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (47 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (48 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (49 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (50 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (51 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (52 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (53 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (54 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (55 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (56 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (57 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (58 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (59 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (60 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (61 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (62 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (63 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)

theorem nodeMetadataSlice001 : FinSlice NodeMetadata 64 64 := by
  intro i hi
  fin_cases i
  · exact (show NodeMetadata (64 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (65 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (66 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (67 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (68 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (69 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (70 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (71 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (72 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (73 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (74 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (75 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (76 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (77 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (78 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (79 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (80 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (81 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (82 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (83 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (84 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (85 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (86 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (87 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (88 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (89 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (90 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (91 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (92 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (93 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (94 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (95 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (96 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (97 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (98 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (99 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (100 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (101 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (102 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (103 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (104 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (105 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (106 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (107 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (108 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (109 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (110 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (111 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (112 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (113 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (114 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (115 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (116 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (117 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (118 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (119 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (120 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (121 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (122 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (123 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (124 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (125 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (126 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (127 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)

theorem nodeMetadataSlice002 : FinSlice NodeMetadata 128 64 := by
  intro i hi
  fin_cases i
  · exact (show NodeMetadata (128 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (129 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (130 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (131 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (132 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (133 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (134 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (135 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (136 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (137 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (138 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (139 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (140 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (141 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (142 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (143 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (144 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (145 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (146 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (147 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (148 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (149 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (150 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (151 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (152 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (153 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (154 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (155 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (156 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (157 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (158 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (159 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (160 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (161 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (162 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (163 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (164 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (165 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (166 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (167 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (168 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (169 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (170 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (171 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (172 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (173 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (174 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (175 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (176 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (177 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (178 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (179 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (180 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (181 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (182 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (183 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (184 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (185 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (186 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (187 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (188 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (189 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (190 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (191 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)

theorem nodeMetadataSlice003 : FinSlice NodeMetadata 192 64 := by
  intro i hi
  fin_cases i
  · exact (show NodeMetadata (192 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (193 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (194 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (195 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (196 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (197 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (198 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (199 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (200 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (201 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (202 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (203 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (204 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (205 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (206 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (207 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (208 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (209 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (210 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (211 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (212 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (213 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (214 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (215 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (216 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (217 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (218 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (219 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (220 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (221 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (222 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (223 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (224 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (225 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (226 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (227 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (228 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (229 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (230 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (231 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (232 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (233 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (234 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (235 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (236 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (237 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (238 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (239 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (240 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (241 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (242 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (243 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (244 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (245 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (246 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (247 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (248 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (249 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (250 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (251 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (252 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (253 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (254 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (255 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
