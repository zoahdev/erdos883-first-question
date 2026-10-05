import Erdos883AdaptiveSpan115021Level3TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength115021_3 : adaptiveNumericSpans115021_3.length = 663 := by decide +kernel
theorem adaptiveSpanEvenCache115021_3 : adaptiveSpanEven115021_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain115021_3 : adaptiveSpanEven115021_3.domainCheck 57511 = true := by decide +kernel
theorem adaptiveSpanEvenEntries115021_3 : adaptiveSpanEven115021_3.spans = coreEvenSpans 57511 0 adaptiveNumericSpans115021_3 := by
  decide +kernel
theorem adaptiveSpanWholeCache115021_3 : adaptiveSpanWhole115021_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain115021_3 : adaptiveSpanWhole115021_3.domainCheck 57511 = true := by decide +kernel
theorem adaptiveSpanWholeEntries115021_3 : adaptiveSpanWhole115021_3.spans = coreWholeSpans 0 adaptiveNumericSpans115021_3 := by
  decide +kernel
end Erdos883Verified
