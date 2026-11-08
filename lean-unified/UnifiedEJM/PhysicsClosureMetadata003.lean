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

theorem nodeMetadataSlice012 : FinSlice NodeMetadata 768 64 := by
  intro i hi
  fin_cases i
  · exact (show NodeMetadata (768 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (769 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (770 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (771 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (772 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (773 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (774 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (775 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (776 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (777 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (778 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (779 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (780 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (781 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (782 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (783 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (784 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (785 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (786 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (787 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (788 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (789 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (790 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (791 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (792 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (793 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (794 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (795 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (796 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (797 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (798 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (799 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (800 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (801 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (802 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (803 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (804 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (805 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (806 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (807 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (808 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (809 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (810 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (811 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (812 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (813 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (814 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (815 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (816 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (817 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (818 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (819 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (820 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (821 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (822 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (823 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (824 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (825 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (826 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (827 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (828 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (829 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (830 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (831 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)

theorem nodeMetadataSlice013 : FinSlice NodeMetadata 832 64 := by
  intro i hi
  fin_cases i
  · exact (show NodeMetadata (832 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (833 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (834 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (835 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (836 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (837 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (838 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (839 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (840 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (841 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (842 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (843 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (844 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (845 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (846 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (847 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (848 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (849 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (850 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (851 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (852 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (853 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (854 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (855 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (856 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (857 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (858 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (859 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (860 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (861 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (862 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (863 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (864 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (865 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (866 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (867 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (868 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (869 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (870 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (871 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (872 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (873 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (874 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (875 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (876 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (877 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (878 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (879 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (880 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (881 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (882 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (883 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (884 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (885 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (886 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (887 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (888 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (889 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (890 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (891 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (892 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (893 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (894 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (895 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)

theorem nodeMetadataSlice014 : FinSlice NodeMetadata 896 64 := by
  intro i hi
  fin_cases i
  · exact (show NodeMetadata (896 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (897 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (898 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (899 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (900 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (901 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (902 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (903 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (904 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (905 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (906 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (907 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (908 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (909 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (910 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (911 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (912 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (913 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (914 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (915 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (916 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (917 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (918 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (919 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (920 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (921 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (922 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (923 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (924 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (925 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (926 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (927 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (928 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (929 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (930 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (931 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (932 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (933 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (934 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (935 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (936 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (937 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (938 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (939 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (940 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (941 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (942 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (943 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (944 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (945 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (946 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (947 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (948 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (949 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (950 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (951 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (952 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (953 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (954 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (955 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (956 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (957 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (958 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (959 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)

theorem nodeMetadataSlice015 : FinSlice NodeMetadata 960 64 := by
  intro i hi
  fin_cases i
  · exact (show NodeMetadata (960 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (961 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (962 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (963 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (964 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (965 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (966 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (967 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (968 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (969 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (970 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (971 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (972 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (973 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (974 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (975 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (976 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (977 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (978 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (979 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (980 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (981 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (982 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (983 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (984 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (985 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (986 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (987 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (988 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (989 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (990 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (991 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (992 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (993 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (994 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (995 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (996 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (997 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (998 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (999 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1000 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1001 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1002 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1003 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1004 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1005 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1006 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1007 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1008 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1009 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1010 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1011 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1012 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1013 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1014 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1015 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1016 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1017 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1018 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1019 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1020 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1021 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1022 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)
  · exact (show NodeMetadata (1023 : Fin 1756) from by
      unfold NodeMetadata
      intro c
      cases c <;> constructor <;> rfl)


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
