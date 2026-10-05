import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_50 :
    (List.ofFn coreChunks680_50).flatten =
      (coreData680.take (coreResources680 50).q).drop 104 := by
  decide +kernel

theorem coreCheck680_50 :
    ∀ c : Fin 1, (coreChunks680_50 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 50)) = true := by
  decide +kernel
#print axioms coreFlatten680_50
#print axioms coreCheck680_50
end Erdos883Verified
