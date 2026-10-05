import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_125 :
    (List.ofFn coreChunks908_125).flatten =
      (coreData908.take (coreResources908 125).q).drop 214 := by
  decide +kernel

theorem coreCheck908_125 :
    ∀ c : Fin 1, (coreChunks908_125 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 125)) = true := by
  decide +kernel
#print axioms coreFlatten908_125
#print axioms coreCheck908_125
end Erdos883Verified
