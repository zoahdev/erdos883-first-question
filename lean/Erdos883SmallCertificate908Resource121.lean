import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_121 :
    (List.ofFn coreChunks908_121).flatten =
      (coreData908.take (coreResources908 121).q).drop 205 := by
  decide +kernel

theorem coreCheck908_121 :
    ∀ c : Fin 1, (coreChunks908_121 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 121)) = true := by
  decide +kernel
#print axioms coreFlatten908_121
#print axioms coreCheck908_121
end Erdos883Verified
