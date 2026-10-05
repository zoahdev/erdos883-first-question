import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_27 :
    (List.ofFn coreChunks908_27).flatten =
      (coreData908.take (coreResources908 27).q).drop 175 := by
  decide +kernel

theorem coreCheck908_27 :
    ∀ c : Fin 1, (coreChunks908_27 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 27)) = true := by
  decide +kernel
#print axioms coreFlatten908_27
#print axioms coreCheck908_27
end Erdos883Verified
