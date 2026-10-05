import Erdos883AdaptiveSpan115021Level5TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength115021_5 : adaptiveNumericSpans115021_5.length = 663 := by decide +kernel
theorem adaptiveSpanEvenCache115021_5 : adaptiveSpanEven115021_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain115021_5 : adaptiveSpanEven115021_5.domainCheck 57511 = true := by decide +kernel
theorem adaptiveSpanEvenEntries115021_5 : adaptiveSpanEven115021_5.spans = coreEvenSpans 57511 0 adaptiveNumericSpans115021_5 := by
  decide +kernel
theorem adaptiveSpanWholeCache115021_5 : adaptiveSpanWhole115021_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain115021_5 : adaptiveSpanWhole115021_5.domainCheck 57511 = true := by decide +kernel
theorem adaptiveSpanWholeEntries115021_5 : adaptiveSpanWhole115021_5.spans = coreWholeSpans 0 adaptiveNumericSpans115021_5 := by
  decide +kernel
end Erdos883Verified
