import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_6 :
    (List.ofFn coreChunks908_6).flatten =
      (coreData908.take (coreResources908 6).q).drop 118 := by
  decide +kernel

theorem coreCheck908_6 :
    ∀ c : Fin 1, (coreChunks908_6 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 6)) = true := by
  decide +kernel
#print axioms coreFlatten908_6
#print axioms coreCheck908_6
end Erdos883Verified
