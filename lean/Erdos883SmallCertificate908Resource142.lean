import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_142 :
    (List.ofFn coreChunks908_142).flatten =
      (coreData908.take (coreResources908 142).q).drop 270 := by
  decide +kernel

theorem coreCheck908_142 :
    ∀ c : Fin 1, (coreChunks908_142 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 142)) = true := by
  decide +kernel
#print axioms coreFlatten908_142
#print axioms coreCheck908_142
end Erdos883Verified
