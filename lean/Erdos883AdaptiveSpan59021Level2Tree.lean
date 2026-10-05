import Erdos883AdaptiveSpan59021Level2TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength59021_2 : adaptiveNumericSpans59021_2.length = 555 := by decide +kernel
theorem adaptiveSpanEvenCache59021_2 : adaptiveSpanEven59021_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain59021_2 : adaptiveSpanEven59021_2.domainCheck 29511 = true := by decide +kernel
theorem adaptiveSpanEvenEntries59021_2 : adaptiveSpanEven59021_2.spans = coreEvenSpans 29511 0 adaptiveNumericSpans59021_2 := by
  decide +kernel
theorem adaptiveSpanWholeCache59021_2 : adaptiveSpanWhole59021_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain59021_2 : adaptiveSpanWhole59021_2.domainCheck 29511 = true := by decide +kernel
theorem adaptiveSpanWholeEntries59021_2 : adaptiveSpanWhole59021_2.spans = coreWholeSpans 0 adaptiveNumericSpans59021_2 := by
  decide +kernel
end Erdos883Verified
