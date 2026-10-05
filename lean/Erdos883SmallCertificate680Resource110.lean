import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_110 :
    (List.ofFn coreChunks680_110).flatten =
      (coreData680.take (coreResources680 110).q).drop 215 := by
  decide +kernel

theorem coreCheck680_110 :
    ∀ c : Fin 1, (coreChunks680_110 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 110)) = true := by
  decide +kernel
#print axioms coreFlatten680_110
#print axioms coreCheck680_110
end Erdos883Verified
