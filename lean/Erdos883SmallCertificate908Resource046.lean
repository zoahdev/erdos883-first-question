import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_46 :
    (List.ofFn coreChunks908_46).flatten =
      (coreData908.take (coreResources908 46).q).drop 199 := by
  decide +kernel

theorem coreCheck908_46 :
    ∀ c : Fin 1, (coreChunks908_46 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 46)) = true := by
  decide +kernel
#print axioms coreFlatten908_46
#print axioms coreCheck908_46
end Erdos883Verified
