import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_30 :
    (List.ofFn coreChunks908_30).flatten =
      (coreData908.take (coreResources908 30).q).drop 179 := by
  decide +kernel

theorem coreCheck908_30 :
    ∀ c : Fin 1, (coreChunks908_30 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 30)) = true := by
  decide +kernel
#print axioms coreFlatten908_30
#print axioms coreCheck908_30
end Erdos883Verified
