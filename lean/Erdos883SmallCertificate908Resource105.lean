import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten908_105 :
    (List.ofFn coreChunks908_105).flatten =
      (coreData908.take (coreResources908 105).q).drop 183 := by
  decide +kernel

theorem coreCheck908_105 :
    ∀ c : Fin 1, (coreChunks908_105 c).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 105)) = true := by
  decide +kernel
#print axioms coreFlatten908_105
#print axioms coreCheck908_105
end Erdos883Verified
