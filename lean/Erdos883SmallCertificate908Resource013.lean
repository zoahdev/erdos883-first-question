import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_13 :
    (List.ofFn coreChunks908_13).flatten =
      (coreData908.take (coreResources908 13).q).drop 157 := by
  decide +kernel

theorem coreCheck908_13 :
    ∀ c : Fin 1, (coreChunks908_13 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 13)) = true := by
  decide +kernel
#print axioms coreFlatten908_13
#print axioms coreCheck908_13
end Erdos883Verified
