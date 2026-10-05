import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_101 :
    (List.ofFn coreChunks680_101).flatten =
      (coreData680.take (coreResources680 101).q).drop 190 := by
  decide +kernel

theorem coreCheck680_101 :
    ∀ c : Fin 1, (coreChunks680_101 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 101)) = true := by
  decide +kernel
#print axioms coreFlatten680_101
#print axioms coreCheck680_101
end Erdos883Verified
