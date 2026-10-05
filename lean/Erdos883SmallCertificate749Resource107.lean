import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten749_107 :
    (List.ofFn coreChunks749_107).flatten =
      (coreData749.take (coreResources749 107).q).drop 191 := by
  decide +kernel

theorem coreCheck749_107 :
    ∀ c : Fin 1, (coreChunks749_107 c).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 107)) = true := by
  decide +kernel
#print axioms coreFlatten749_107
#print axioms coreCheck749_107
end Erdos883Verified
