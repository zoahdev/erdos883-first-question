import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_105 :
    (List.ofFn coreChunks749_105).flatten =
      (coreData749.take (coreResources749 105).q).drop 189 := by
  decide +kernel

theorem coreCheck749_105 :
    ∀ c : Fin 1, (coreChunks749_105 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 105)) = true := by
  decide +kernel
#print axioms coreFlatten749_105
#print axioms coreCheck749_105
end Erdos883Verified
