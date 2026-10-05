import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_55 :
    (List.ofFn coreChunks908_55).flatten =
      (coreData908.take (coreResources908 55).q).drop 210 := by
  decide +kernel

theorem coreCheck908_55 :
    ∀ c : Fin 1, (coreChunks908_55 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 55)) = true := by
  decide +kernel
#print axioms coreFlatten908_55
#print axioms coreCheck908_55
end Erdos883Verified
