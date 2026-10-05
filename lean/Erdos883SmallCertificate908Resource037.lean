import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_37 :
    (List.ofFn coreChunks908_37).flatten =
      (coreData908.take (coreResources908 37).q).drop 188 := by
  decide +kernel

theorem coreCheck908_37 :
    ∀ c : Fin 1, (coreChunks908_37 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 37)) = true := by
  decide +kernel
#print axioms coreFlatten908_37
#print axioms coreCheck908_37
end Erdos883Verified
