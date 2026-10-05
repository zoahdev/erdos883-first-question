import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_76 :
    (List.ofFn coreChunks908_76).flatten =
      (coreData908.take (coreResources908 76).q).drop 141 := by
  decide +kernel

theorem coreCheck908_76 :
    ∀ c : Fin 1, (coreChunks908_76 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 76)) = true := by
  decide +kernel
#print axioms coreFlatten908_76
#print axioms coreCheck908_76
end Erdos883Verified
