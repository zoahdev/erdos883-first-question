import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_77 :
    (List.ofFn coreChunks749_77).flatten =
      (coreData749.take (coreResources749 77).q).drop 139 := by
  decide +kernel

theorem coreCheck749_77 :
    ∀ c : Fin 1, (coreChunks749_77 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 77)) = true := by
  decide +kernel
#print axioms coreFlatten749_77
#print axioms coreCheck749_77
end Erdos883Verified
