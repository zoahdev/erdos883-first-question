import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_128 :
    (List.ofFn coreChunks908_128).flatten =
      (coreData908.take (coreResources908 128).q).drop 226 := by
  decide +kernel

theorem coreCheck908_128 :
    ∀ c : Fin 1, (coreChunks908_128 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 128)) = true := by
  decide +kernel
#print axioms coreFlatten908_128
#print axioms coreCheck908_128
end Erdos883Verified
