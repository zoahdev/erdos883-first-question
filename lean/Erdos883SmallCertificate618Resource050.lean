import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_50 :
    (List.ofFn coreChunks618_50).flatten =
      (coreData618.take (coreResources618 50).q).drop 104 := by
  decide +kernel

theorem coreCheck618_50 :
    ∀ c : Fin 1, (coreChunks618_50 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 50)) = true := by
  decide +kernel
#print axioms coreFlatten618_50
#print axioms coreCheck618_50
end Erdos883Verified
