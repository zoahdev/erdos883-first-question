import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_92 :
    (List.ofFn coreChunks908_92).flatten =
      (coreData908.take (coreResources908 92).q).drop 164 := by
  decide +kernel

theorem coreCheck908_92 :
    ∀ c : Fin 1, (coreChunks908_92 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 92)) = true := by
  decide +kernel
#print axioms coreFlatten908_92
#print axioms coreCheck908_92
end Erdos883Verified
