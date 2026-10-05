import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_64 :
    (List.ofFn coreChunks618_64).flatten =
      (coreData618.take (coreResources618 64).q).drop 130 := by
  decide +kernel

theorem coreCheck618_64 :
    ∀ c : Fin 1, (coreChunks618_64 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 64)) = true := by
  decide +kernel
#print axioms coreFlatten618_64
#print axioms coreCheck618_64
end Erdos883Verified
