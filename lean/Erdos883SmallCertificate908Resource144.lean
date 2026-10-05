import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_144 :
    (List.ofFn coreChunks908_144).flatten =
      (coreData908.take (coreResources908 144).q).drop 273 := by
  decide +kernel

theorem coreCheck908_144 :
    ∀ c : Fin 1, (coreChunks908_144 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 144)) = true := by
  decide +kernel
#print axioms coreFlatten908_144
#print axioms coreCheck908_144
end Erdos883Verified
