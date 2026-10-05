import Erdos883AdaptiveSpan59021Level9TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength59021_9 : adaptiveNumericSpans59021_9.length = 555 := by decide +kernel
theorem adaptiveSpanEvenCache59021_9 : adaptiveSpanEven59021_9.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain59021_9 : adaptiveSpanEven59021_9.domainCheck 29511 = true := by decide +kernel
theorem adaptiveSpanEvenEntries59021_9 : adaptiveSpanEven59021_9.spans = coreEvenSpans 29511 0 adaptiveNumericSpans59021_9 := by
  decide +kernel
theorem adaptiveSpanWholeCache59021_9 : adaptiveSpanWhole59021_9.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain59021_9 : adaptiveSpanWhole59021_9.domainCheck 29511 = true := by decide +kernel
theorem adaptiveSpanWholeEntries59021_9 : adaptiveSpanWhole59021_9.spans = coreWholeSpans 0 adaptiveNumericSpans59021_9 := by
  decide +kernel
end Erdos883Verified
