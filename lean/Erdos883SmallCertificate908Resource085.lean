import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_85 :
    (List.ofFn coreChunks908_85).flatten =
      (coreData908.take (coreResources908 85).q).drop 154 := by
  decide +kernel

theorem coreCheck908_85 :
    ∀ c : Fin 1, (coreChunks908_85 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 85)) = true := by
  decide +kernel
#print axioms coreFlatten908_85
#print axioms coreCheck908_85
end Erdos883Verified
